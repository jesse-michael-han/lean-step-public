import collections
import hashlib
import os

from mpmath import mp, mpf, fmod

mp.dps = 50


def hash_string_to_int(arg):
    return int(hashlib.sha256(arg.encode("utf-8")).hexdigest(), 16) % 10 ** 30


def hash_string_to_float(arg):
    x = mpf(hash_string_to_int(arg))
    return fmod(x * mp.pi, mpf(1.0))


def get_split(arg, train_threshold, valid_threshold):
    float_hash = hash_string_to_float(arg.split()[0])
    if float_hash < train_threshold:
        return "train"
    elif float_hash < valid_threshold:
        return "valid"
    else:
        return "test"


def _parse_main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("decls_file")
    parser.add_argument("dest_dir")
    parser.add_argument("--train_threshold", type=float, default=0.92)
    parser.add_argument("--valid_threshold", type=float, default=0.96)
    return parser.parse_args()


def _main(decls_file: str, dest_dir: str, train_threshold: float, valid_threshold: float):
    with open(decls_file, "r") as f:
        decls = f.readlines()
    dataset = collections.defaultdict(list)
    for decl in decls:
        dataset[get_split(decl, train_threshold=train_threshold, valid_threshold=valid_threshold)].append(decl)

    if not os.path.exists(dest_dir):
        os.makedirs(dest_dir)
    for split in ["train", "valid", "test"]:
        with open(os.path.join(dest_dir, f"{split}_decls.log"), "w") as f:
            for decl in dataset[split]:
                f.write(decl)


if __name__ == "__main__":
    opts = _parse_main()
    _main(**vars(opts))
