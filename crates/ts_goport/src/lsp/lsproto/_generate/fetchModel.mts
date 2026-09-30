#!/usr/bin/env -S node --experimental-strip-types

// Usage: node --experimental-strip-types fetchModel.mts

// PORT: port of microsoft/TypeScript tsc/internal/lsp/lsproto/_generate/fetchModel.mts
// (pinned 673a5f17d713). Go reads the vscode-languageclient version from the
// repository package-lock.json. This crate has no package-lock, so the ref is
// fixed to the version that the pinned Go lock file names (10.1.1 at
// 673a5f17d713). Both downloads are checked against their pinned sha256 values
// before use.

import crypto from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import url from "node:url";

const __filename = url.fileURLToPath(new URL(import.meta.url));
const __dirname = path.dirname(__filename);

const metaModelPath = path.join(__dirname, "metaModel.json");
const metaModelSchemaPath = path.join(__dirname, "metaModelSchema.mts");

// PORT: fixed version (Go: package-lock.json "node_modules/vscode-languageclient").
const clientVersion = "10.1.1";

// Pinned sha256 of the two downloads at this ref.
const metaModelSha256 = "caae8df639a4248520a3f589fd72945365e9d8ebca5baf564161a515430d9d41";
const metaModelSchemaSha256 = "34adc4972d75a29af15992a95157add17eb6a4c8820fbc2a47850fb84f3170ae";

const ref = `release/client/${clientVersion}`;
console.log(`Using vscode-languageclient@${clientVersion}`);

const metaModelURL = `https://raw.githubusercontent.com/microsoft/vscode-languageserver-node/${ref}/protocol/metaModel.json`;
const metaModelSchemaURL = `https://raw.githubusercontent.com/microsoft/vscode-languageserver-node/${ref}/tools/src/metaModel.ts`;

// checkSha256 stops the script when the downloaded text is not the pinned file.
function checkSha256(name: string, text: string, expected: string) {
    const actual = crypto.createHash("sha256").update(text, "utf-8").digest("hex");
    if (actual !== expected) {
        console.error(`${name}: sha256 ${actual} does not match the pinned ${expected}`);
        process.exit(1);
    }
}

const metaModelResponse = await fetch(metaModelURL);
const metaModel = await metaModelResponse.text();
checkSha256("metaModel.json", metaModel, metaModelSha256);
fs.writeFileSync(metaModelPath, metaModel);

const metaModelSchemaResponse = await fetch(metaModelSchemaURL);
let metaModelSchema = await metaModelSchemaResponse.text();
checkSha256("metaModel.ts", metaModelSchema, metaModelSchemaSha256);

// Patch the schema to add omitzeroValue property to Property type
metaModelSchema = metaModelSchema.replace(
    /(\t \* Whether the property is deprecated or not\. If deprecated\n\t \* the property contains the deprecation message\.\n\t \*\/\n\tdeprecated\?: string;)\n}/m,
    `$1\n\n\t/**\n\t * Whether this property uses omitzero without being a pointer.\n\t * Custom extension for special value types.\n\t */\n\tomitzeroValue?: boolean;\n}`,
);

fs.writeFileSync(metaModelSchemaPath, metaModelSchema);
