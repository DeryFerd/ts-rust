import assert from "node:assert/strict";
import { test } from "node:test";
import { memoryFileSystem } from "../core.js";

test("in-memory stat reports UTF-8 byte sizes", () => {
    const cases = [["", 0], ["hello", 5], ["é", 2], ["€", 3], ["😀", 4], ["Aé€😀", 10], ["\uFEFFé", 5]];
    for (const [text, size] of cases) {
        const fs = memoryFileSystem({ "/a.ts": text });
        assert.deepEqual(fs.stat("/a.ts"), { isDirectory: false, size, mtimeMs: 0 }, JSON.stringify(text));
    }
});

test("in-memory stat reports updated byte sizes after writes and appends", () => {
    const fs = memoryFileSystem();
    const encoder = new TextEncoder();
    fs.writeFile("/out/a.js", encoder.encode("\uFEFFé"), false);
    assert.equal(fs.files.get("/out/a.js"), "\uFEFFé");
    assert.equal(fs.stat("/out/a.js").size, 5);

    fs.writeFile("/out/a.js", encoder.encode("😀"), true);
    assert.equal(fs.files.get("/out/a.js"), "\uFEFFé😀");
    assert.equal(fs.stat("/out/a.js").size, 9);

    fs.writeFile("/out/a.js", encoder.encode("x"), false);
    assert.equal(fs.stat("/out/a.js").size, 1);
});
