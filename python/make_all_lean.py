import json
import os
from pathlib import Path
import subprocess


SOURCE_SUFFIX_IGNORE = [
    "library",
    "/./src",
    "lean-gptf/src",
    "lean-tpe/src",
]


def _main():
    # delete src/all.lean
    print()
    print("====================")
    print("Clean `src/all.lean`")
    print("====================")
    all_lean = Path("src/all.lean")
    if all_lean.exists():
        os.remove(Path("src/all.lean"))
        print("src/all.lean removed.")

    # generate all.lean
    print("")
    print("=====================")
    print("Generate src/all.lean")
    print("=====================")
    print("Getting lean paths.")
    with subprocess.Popen(
        ["lean", "--path"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    ) as out:
        stdout, stderr = out.communicate()
    assert stderr is None, stderr
    s = stdout.decode("utf-8")
    path_data = json.loads(s)

    imports = []
    for p in path_data["path"]:
        skip = False
        for s in SOURCE_SUFFIX_IGNORE:
            if p.endswith(s):
                skip = True
        if skip:
            print("Skipping: ", p)
        else:
            print("Found path: ", p)
            pp = Path(p)
            for file_name in pp.glob("**/*.lean"):
                i = "import " + str(file_name)[len(p) + 1 : -5].replace("/", ".")
                imports += [i]
    with open("src/all.lean", "w") as w:
        for i in sorted(imports):
            w.write(f"{i}\n")


if __name__ == "__main__":
    _main()
