"""Generate native-core expectations consumed by every WASM host test."""

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
requests = [
    {"script": "#!/bin/sh\nprintf '%s\\n' hello\n"},
    {"script": "#!/bin/sh\necho $value\n"},
    {"script": "#!/bin/bash\necho café\n\techo $value\n", "filename": "脚本.sh"},
    {"script": "if true; then\n"},
    {
        "script": "#!/bin/sh\n. shared.sh\necho $shared",
        "files": {"shared.sh": "shared=hello\n"},
    },
    {
        "script": "#!/bin/sh\n. shared.sh\n",
        "files": {"shared.sh": "echo $missing\n"},
        "checkSourced": True,
    },
    {"script": "#!/bin/sh\n. shared.sh\n"},
    {"script": "#!/bin/sh\necho $value", "exclude": [2086]},
    {"script": "#!/bin/sh\necho $value", "include": [2086]},
    {"script": "#!/bin/sh\necho $value", "severity": "warning"},
    {"script": "echo $value", "extendedAnalysis": False},
    {
        "script": "#!/bin/bash\nx=1; echo $x",
        "optionalChecks": ["require-variable-braces"],
    },
    {"script": "#!/bin/sh\nset -a\nunused=1"},
    {"script": "#!/bin/sh\nsed -n -e '/foo/h; ${ g; }'"},
    {
        "script": "#!/bin/bash\nf() { if true; then cd /missing; echo continued; fi; }\nf"
    },
    {"script": "#" + "x" * 200_000 + "\ntrue\n", "shell": "sh"},
    {"script": "#!/bin/sh\ntrue\n"},
    *(
        {"script": "echo $x; [[ -n $x ]]", "shell": shell}
        for shell in ("sh", "bash", "dash", "ksh", "busybox")
    ),
    {"script": "true", "shell": "invalid"},
    {"script": "true", "unexpected": True},
    {"script": "true", "severity": "invalid"},
    {},
]
fixtures = []
for request in requests:
    result = subprocess.run(
        [str(ROOT / "target/release/examples/check")],
        input=json.dumps(request),
        text=True,
        capture_output=True,
        check=True,
    )
    fixtures.append({"request": request, "result": json.loads(result.stdout)})
out = ROOT / ".cache/wasm-parity.json"
out.parent.mkdir(exist_ok=True)
out.write_text(json.dumps(fixtures), encoding="utf-8")
print(f"Wrote {len(fixtures)} native parity cases to {out}")
