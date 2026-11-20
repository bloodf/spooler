"""Import the plugin outside OrcaSlicer, with a stand-in for the embedded `orca` module.

The plugin is the package plugin/spooler/, one module per domain. load() hands tests one object that reads and sets
a name on the module that defines it, so `sp.name` and `mock.patch.object(sp, "name")` work whichever module holds it.
"""

import importlib.util
import os
import socket
import sys
import tempfile
import types
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent.parent / "plugin" / "spooler"
PACKAGE_NAME = "spooler_plugin"   # not "spooler": the wheel test imports the built package under its real name


class _Base:
    def __init__(self, *args, **kwargs):
        pass

    def post_message(self, data):
        self.posted = getattr(self, "posted", []) + [data]


def _stub_orca() -> types.ModuleType:
    orca = types.ModuleType("orca")
    orca.base = _Base
    orca.decorated = []
    orca.plugin = lambda cls: orca.decorated.append(cls) or cls
    orca.register_capability = lambda cls: None
    orca.PluginType = types.SimpleNamespace(Pages="Pages")
    orca.ExecutionResult = types.SimpleNamespace(success=lambda *a, **k: ("success", a),
                                                 failure=lambda *a, **k: ("failure", a))
    orca.PluginResult = types.SimpleNamespace(RecoverableError="RecoverableError")
    orca.script = types.SimpleNamespace(ScriptPluginCapabilityBase=_Base)
    orca.slicing = types.SimpleNamespace(SlicingPipelineCapabilityBase=_Base,
                                         Step=types.SimpleNamespace(psGCodePostProcess=1, posSlice=2))
    pages = types.ModuleType("orca.pages")
    pages.PagesPluginCapabilityBase = _Base
    orca.pages = pages
    reloads: list[str] = []
    orca.reloads = reloads
    orca.host = types.SimpleNamespace(
        ui=types.SimpleNamespace(message=lambda *a, **k: None),
        preset=types.SimpleNamespace(bundles=types.SimpleNamespace(reload_local=reloads.append)),
    )
    sys.modules["orca"] = orca
    sys.modules["orca.pages"] = pages
    return orca


_HOME = tempfile.mkdtemp(prefix="spooler-tests-")

# No test may reach a real printer, Spoolman or Moonraker. Every outgoing connection the plugin (or
# urllib, http.client, ssl and ftplib under it) makes goes through socket.create_connection, so the
# guard sits there, installed once by load() for the whole run whatever the test order. Loopback stays
# open for the fake servers some tests start on 127.0.0.1.
LOOPBACK = ("127.0.0.1", "::1", "localhost")
_real_create_connection = socket.create_connection


def guarded_create_connection(address, *args, **kwargs):
    if not (isinstance(address, tuple) and address and address[0] in LOOPBACK):
        raise AssertionError(f"network forbidden in these tests: {address!r}")
    return _real_create_connection(address, *args, **kwargs)


def install_network_guard() -> None:
    socket.create_connection = guarded_create_connection


def load():
    """(plugin module, stub orca module). The plugin's settings and log go to a temporary
    folder, never to a real OrcaSlicer install, and the network guard is on."""
    install_network_guard()
    for key in ("HOME", "APPDATA", "XDG_CONFIG_HOME"):
        os.environ[key] = _HOME
    orca = _stub_orca()
    # A fresh copy for every caller, as the single-file plugin was: each test file gets its own module state.
    for name in [n for n in sys.modules if n == PACKAGE_NAME or n.startswith(PACKAGE_NAME + ".")]:
        del sys.modules[name]
    spec = importlib.util.spec_from_file_location(PACKAGE_NAME, PACKAGE / "__init__.py",
                                                  submodule_search_locations=[str(PACKAGE)])
    package = importlib.util.module_from_spec(spec)
    sys.modules[PACKAGE_NAME] = package
    spec.loader.exec_module(package)
    return Plugin(package), orca


def sources() -> dict[str, str]:
    """{module file name: source} of every module of the plugin package."""
    return {f.name: f.read_text(encoding="utf-8") for f in sorted(PACKAGE.glob("*.py"))}


class Plugin:
    """The plugin package seen as one namespace: a name is read from, set on and deleted from the module that
    defines it (or every module that imported it, for a shared import), so a patch reaches every caller."""

    def __init__(self, package):
        modules = [package] + [getattr(package, n) for n in sorted(vars(package))
                               if isinstance(getattr(package, n), types.ModuleType)
                               and getattr(package, n).__name__.startswith(package.__name__ + ".")]
        object.__setattr__(self, "_package", package)
        object.__setattr__(self, "_modules", modules[1:])
        object.__setattr__(self, "_deleted", {})   # name -> its modules, so mock.patch can put it back after a delete

    def _owners(self, name):
        mods = object.__getattribute__(self, "_modules")
        return [m for m in mods if name in vars(m)]

    def __getattr__(self, name):
        for module in self._owners(name):
            return vars(module)[name]
        return getattr(object.__getattribute__(self, "_package"), name)

    def __setattr__(self, name, value):
        owners = self._owners(name) or object.__getattribute__(self, "_deleted").pop(name, [])
        if not owners:
            raise AttributeError(f"no plugin module defines {name!r}")
        for module in owners:
            setattr(module, name, value)

    def __delattr__(self, name):
        owners = self._owners(name)
        if not owners:
            raise AttributeError(name)
        object.__getattribute__(self, "_deleted")[name] = owners
        for module in owners:
            delattr(module, name)
