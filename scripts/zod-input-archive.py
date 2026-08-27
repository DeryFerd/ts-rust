"""Inspect pinned Zod input archives, then extract into an empty directory."""

import base64
import hashlib
import hmac
import json
import os
from pathlib import Path
import stat
import sys
import tarfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checked_name(name):
    require(isinstance(name, str) and name, "Empty archive path")
    require("\\" not in name and "\0" not in name, f"Unsafe archive path: {name!r}")
    require(
        all(part not in ("", ".", "..") for part in name.split("/")),
        f"Unsafe archive path: {name!r}",
    )
    return name


def parents(name):
    parts = name.split("/")
    return ["/".join(parts[:index]) for index in range(1, len(parts))]


def check_link(name, nodes):
    # Resolve archive links without touching the host filesystem.
    pending = name.split("/")
    resolved = []
    hops = 0
    while pending:
        part = pending.pop(0)
        if part in ("", "."):
            continue
        if part == "..":
            require(resolved, f"Archive link leaves its root: {name}")
            resolved.pop()
            continue
        candidate = "/".join([*resolved, part])
        member = nodes.get(candidate)
        if member is not None and member.issym():
            hops += 1
            require(hops <= 40, f"Archive link cycle: {name}")
            pending = member.linkname.split("/") + pending
        else:
            resolved.append(part)


def inspect(archive, request):
    prefix = request["prefix"]
    if prefix:
        checked_name(prefix)
    nodes = {}
    seen = set()
    total_bytes = 0
    for member in archive.getmembers():
        raw = (
            member.name[:-1]
            if member.isdir() and member.name.endswith("/")
            else member.name
        )
        checked_name(raw)
        require(raw not in seen, f"Duplicate archive path: {raw}")
        seen.add(raw)
        require(len(seen) <= 100_000, "Too many archive entries")
        require(
            member.isdir() or member.isreg() or member.issym(),
            f"Unsupported archive entry: {raw}",
        )
        require(not member.issparse(), f"Sparse archive file: {raw}")
        total_bytes += member.size
        require(
            0 <= member.size and total_bytes <= 512 * 1024**2,
            "Archive is too large",
        )
        if prefix and raw == prefix:
            require(member.isdir(), "The archive prefix must be a directory")
            continue
        require(
            not prefix or raw.startswith(prefix + "/"),
            f"Wrong archive prefix: {raw}",
        )
        name = raw[len(prefix) + 1 :] if prefix else raw
        if member.issym():
            target = member.linkname
            require(
                target
                and not target.startswith("/")
                and "\\" not in target
                and "\0" not in target,
                f"Unsafe archive link: {name}",
            )
        nodes[name] = member
    for name, member in nodes.items():
        for parent in parents(name):
            require(
                parent not in nodes or nodes[parent].isdir(),
                f"Archive entry has a non-directory parent: {name}",
            )
        if member.issym():
            check_link(name, nodes)
    selected = request["members"]
    if selected is None:
        selected = list(nodes)
    else:
        require(
            len(selected) == len(set(selected)),
            "Duplicate selected archive member",
        )
        for name in selected:
            checked_name(name)
            require(
                name in nodes and nodes[name].isreg(),
                f"Missing regular archive member: {name}",
            )
    directories = set()
    for name in selected:
        member = nodes[name]
        require(
            request["allowLinks"] or not member.issym(),
            f"Tool archive contains a symlink: {name}",
        )
        directories.update(parents(name))
        if member.isdir():
            directories.add(name)
    return nodes, selected, directories


def empty_destination(name):
    destination = Path(name)
    require(destination.is_absolute(), "Extraction destination must be absolute")
    for entry in [*reversed(destination.parents), destination]:
        mode = entry.lstat().st_mode
        require(
            stat.S_ISDIR(mode),
            f"Symlinked or invalid extraction directory: {entry}",
        )
    require(not any(destination.iterdir()), "Extraction destination is not empty")
    return destination


def read_archive(request):
    with open(3, "rb", closefd=False) as source:
        before = os.fstat(source.fileno())
        require(
            stat.S_ISREG(before.st_mode) and before.st_nlink == 1,
            "Unsafe archive file",
        )
        algorithm, expected = request["integrity"].split("-", 1)
        require(algorithm in ("sha256", "sha512"), "Unsupported archive digest")
        digest = hashlib.file_digest(source, algorithm).digest()
        actual = (
            digest.hex()
            if algorithm == "sha256"
            else base64.b64encode(digest).decode("ascii")
        )
        require(
            hmac.compare_digest(actual, expected),
            "Pinned archive integrity mismatch",
        )
        source.seek(0)
        with tarfile.open(fileobj=source, mode="r:*") as archive:
            nodes, selected, directories = inspect(archive, request)
            destination = (
                empty_destination(request["destination"])
                if request["destination"]
                else None
            )
            if destination:
                for name in sorted(
                    directories, key=lambda name: (name.count("/"), name)
                ):
                    (destination / name).mkdir(mode=0o755)
            result = [{"path": name, "type": "directory"} for name in directories]
            for name in selected:
                member = nodes[name]
                if member.isdir():
                    continue
                if member.issym():
                    result.append(
                        {"path": name, "type": "symlink", "target": member.linkname}
                    )
                    continue
                mode = 0o755 if member.mode & 0o111 else 0o644
                digest = hashlib.sha256()
                written = 0
                target = None
                try:
                    if destination:
                        descriptor = os.open(
                            destination / name,
                            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                            mode,
                        )
                        target = os.fdopen(descriptor, "wb")
                        os.fchmod(descriptor, mode)
                    with archive.extractfile(member) as content:
                        while block := content.read(1024 * 1024):
                            digest.update(block)
                            written += len(block)
                            if target:
                                target.write(block)
                finally:
                    if target:
                        target.close()
                require(written == member.size, f"Incomplete archive file: {name}")
                result.append(
                    {
                        "path": name,
                        "type": "file",
                        "mode": mode,
                        "bytes": written,
                        "sha256": digest.hexdigest(),
                    }
                )
            if destination:
                for name in selected:
                    member = nodes[name]
                    if member.issym():
                        os.symlink(member.linkname, destination / name)
                for name in selected:
                    if nodes[name].issym():
                        require(
                            (destination / name).resolve().is_relative_to(destination),
                            f"Archive link leaves its root: {name}",
                        )
        after = os.fstat(source.fileno())
        require(
            (before.st_size, before.st_mtime_ns, before.st_ctime_ns)
            == (after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            "Archive changed while reading",
        )
        return sorted(result, key=lambda item: item["path"].encode("utf-8"))


if __name__ == "__main__":
    try:
        print(json.dumps(read_archive(json.load(sys.stdin)), separators=(",", ":")))
    except (OSError, ValueError, tarfile.TarError) as error:
        sys.exit(str(error))
