#!/usr/bin/env bash
# Allow only setup-chrome's executable to create its sandbox on Ubuntu runners.
# https://chromium.googlesource.com/chromium/src/+/main/docs/security/apparmor-userns-restrictions.md
set -euo pipefail

[[ "${GITHUB_ACTIONS:-}" == true && "${RUNNER_OS:-}" == Linux ]]
if [[ ! -f /proc/sys/kernel/apparmor_restrict_unprivileged_userns ]] ||
   [[ "$(cat /proc/sys/kernel/apparmor_restrict_unprivileged_userns)" != 1 ]]; then
  exit 0
fi

chrome_path="$(realpath "${CHROME:?CHROME must point to the setup-chrome executable}")"
[[ "$chrome_path" =~ ^/opt/hostedtoolcache/setup-chrome/[a-zA-Z0-9._/-]+/chrome$ ]]
[[ -x "$chrome_path" ]]
profile="$(mktemp)"
trap 'rm -f "$profile"' EXIT
cat > "$profile" <<EOF
abi <abi/4.0>,
include <tunables/global>
profile orca-ci-chrome "$chrome_path" flags=(unconfined) {
  userns,
}
EOF
sudo apparmor_parser -r "$profile"
