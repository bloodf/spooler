"""Import the plugin outside OrcaSlicer, with a stand-in for the embedded `orca` module."""

import importlib.util
import os
import sys
import tempfile
import types
from pathlib import Path

PLUGIN = Path(__file__).resolve().parent.parent / "plugin" / "spooler" / "spooler_any.py"


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


def load():
    """(plugin module, stub orca module). The plugin's settings and log go to a temporary
    folder, never to a real OrcaSlicer install."""
    for key in ("HOME", "APPDATA", "XDG_CONFIG_HOME"):
        os.environ[key] = _HOME
    orca = _stub_orca()
    spec = importlib.util.spec_from_file_location("spooler_plugin", PLUGIN)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module, orca
