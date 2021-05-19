import pickle as pkl
import os
import subprocess
from tqdm import tqdm
from multiprocessing.pool import ThreadPool
from pathlib import Path


def _parse_main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("decls_file")
    parser.add_argument("dest_dir")
    parser.add_argument("n_workers", type=int)
    parser.add_argument("rec_limit", type=int)  # default 5000
    parser.add_argument("depth_limit", type=int)  # default 100
    parser.add_argument("weight_limit", type=int)  # default 2000
    parser.add_argument("decls_per_shard", type=int)
    return parser.parse_args()


def gen_data_step(decl_file: str, dest: str, rec_limit: int, depth_limit: int, weight_limit: int):
    lean_cmd = ["lean"]
    lean_cmd += ["--run"]
    lean_cmd += ["./src/lean_step.lean"]
    lean_cmd += list(map(str, [decl_file, dest, rec_limit, depth_limit, weight_limit]))
    path = Path(dest)
    stdout_dest = os.path.join(str(path.parent), str(path.stem) + ".out")
    with open(stdout_dest, "w") as f:
        subprocess.run(lean_cmd, stdout=f, stderr=f)
    return decl_file


class GenDataState:
    def __init__(self, decl_files):
        self.done_dict = {decl_file: False for decl_file in decl_files}

    def retrieve_tasks(self):
        return [k for k, v in self.done_dict.items() if not v]

    def register_finished(self, decl_file):
        self.done_dict[decl_file] = True


def _main(
    decls_file: str,
    dest_dir: str,
    n_workers: int,
    rec_limit: int,
    decls_per_shard: int,
    depth_limit: int,
    weight_limit: int,
):
    with open(decls_file, "r") as f:
        decls = f.readlines()

    num_shards = len(decls) // decls_per_shard

    batch_size = decls_per_shard

    batches = [decls[i * batch_size : (i + 1) * batch_size] for i in range(num_shards - 1)] + [
        decls[batch_size * (num_shards - 1) :]
    ]

    split_decls_dir = os.path.join(dest_dir, "split_decls/")
    if not os.path.exists(split_decls_dir):
        os.makedirs(split_decls_dir)

    decl_files = []
    for i, batch in enumerate(batches):
        decl_file = os.path.join(split_decls_dir, f"shard_{i}.names")
        with open(decl_file, "w") as f:
            for decl in batch:
                f.write(decl)
        decl_files.append(decl_file)

    gen_data_state_path = os.path.join(dest_dir, "gen_data_state.pkl")

    if os.path.exists(gen_data_state_path):
        with open(gen_data_state_path, "rb") as f:
            gen_data_state = pkl.load(f)
    else:
        gen_data_state = GenDataState(decl_files)

    dests = [os.path.join(dest_dir, f"shard_{i}.json") for i in range(len(batches))]

    pool_args = [
        (decl_file, dest, rec_limit, depth_limit, weight_limit)
        for decl_file, dest in zip(gen_data_state.retrieve_tasks(), dests)
    ]
    with ThreadPool(n_workers) as pool:
        finished_count = 0
        for decl_file in tqdm(
            pool.imap_unordered((lambda x: gen_data_step(*x)), pool_args), total=len(decl_files)
        ):
            finished_count += 1
            print(f"{finished_count} JOBS FINISHED")
            gen_data_state.register_finished(decl_file)
            with open(gen_data_state_path, "wb") as f:
                pkl.dump(gen_data_state, f)


if __name__ == "__main__":
    opts = _parse_main()
    _main(**vars(opts))
