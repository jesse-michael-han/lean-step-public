import os


def files_with_extension(dir_path, ext=None):
    return [
        os.path.join(dir_path, f)
        for f in os.listdir(dir_path)
        if (f.endswith(f".{ext}") if ext is not None else True)
    ]
