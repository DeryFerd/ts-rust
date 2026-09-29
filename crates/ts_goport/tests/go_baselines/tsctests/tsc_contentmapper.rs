//! Port of the typescript-go `internal/execute/tsctests/tsc_test.go` content
//! mapper tests (tsgo#4712): `TestTscContentMapperEmit`,
//! `TestTscContentMapperExplainFiles`, `TestTscContentMapperOptionDiagnostics`,
//! `TestTscContentMapperFailures` and `TestTscContentMapperSynthesized`.
//!
//! PORT: Go backtick literals in `stringtestutil.Dedent` keep their relative
//! indentation here (a Go tab is 4 spaces after `Dedent`). The other
//! literals have no line breaks.

use crate::support::contentmappertest;
use crate::support::runner::{FileMap, TscInput, WatchFilter, run_tsc_inputs};
use crate::support::stringtestutil::dedent;
use crate::support::vfstest::MapFile;

/// Go `FileMap{path: value, ...}`. Each value goes through `MapFile::from`.
macro_rules! files {
    ($($path:expr => $value:expr),* $(,)?) => {{
        let mut map = FileMap::new();
        $(map.insert(String::from($path), MapFile::from($value));)*
        map
    }};
}

/// Go `[]string{...}`.
fn argv(args: &[&str]) -> Vec<String> {
    args.iter().map(std::string::ToString::to_string).collect()
}

// Go: tsc_test.go:4808 TestTscContentMapperEmit
#[test]
fn tsc_content_mapper_emit() {
    let inputs = vec![TscInput {
        sub_scenario: "content-mapped files are not emitted".to_string(),
        files: files! {
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
            {
                "compilerOptions": {
                    "outDir": "./dist"
                },
                "contentMappers": [
                    { "package": "vue-ts-mapper", "extensions": [".vue"] }
                ]
            }"#),
            "/home/src/workspaces/project/index.ts" => "export const local = 1;",
            "/home/src/workspaces/project/app.vue" => "export const app = 1;",
            "/home/src/workspaces/project/node_modules/vue-ts-mapper/package.json" => dedent(r#"
            {
                "name": "vue-ts-mapper",
                "version": "1.0.0",
                "typescript": { "contentMapper": { "exec": ["verbatim-mapper"] } }
            }"#),
        },
        command_line_args: argv(&["--runExternalCode"]),
        ..Default::default()
    }];
    run_tsc_inputs("contentMapperEmit", inputs, WatchFilter::NonWatch);
}

// Go: tsc_test.go:4835 TestTscContentMapperExplainFiles
#[test]
fn tsc_content_mapper_explain_files() {
    let inputs = vec![TscInput {
        sub_scenario: "supplemental virtual file include reason".to_string(),
        files: files! {
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
            {
                "contentMappers": [
                    { "package": "mapper", "extensions": [".vue"] }
                ]
            }"#),
            "/home/src/workspaces/project/app.vue" => "export const value = 1;",
            "/home/src/workspaces/project/node_modules/mapper/package.json" => dedent(r#"
            {
                "name": "mapper",
                "version": "1.0.0",
                "typescript": { "contentMapper": { "exec": ["supplemental-mapper"] } }
            }"#),
        },
        command_line_args: argv(&["--runExternalCode", "--explainFiles"]),
        ..Default::default()
    }];
    run_tsc_inputs("contentMapperExplainFiles", inputs, WatchFilter::NonWatch);
}

// Go: tsc_test.go:4858 TestTscContentMapperOptionDiagnostics
#[test]
fn tsc_content_mapper_option_diagnostics() {
    let inputs = vec![TscInput {
        sub_scenario: "nested mapper option diagnostic".to_string(),
        files: files! {
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
            {
                "contentMappers": [
                    {
                        "package": "mapper",
                        "extensions": [".vue"],
                        "options": { "plugins": [{ "name": 1 }] }
                    }
                ]
            }"#),
            "/home/src/workspaces/project/app.vue" => "export const value = 1;",
            "/home/src/workspaces/project/node_modules/mapper/package.json" =>
                contentmappertest::package_json(contentmappertest::DYNAMIC_VERBATIM_MAPPER),
        },
        command_line_args: argv(&["--runExternalCode", "--pretty", "false"]),
        ..Default::default()
    }];
    run_tsc_inputs(
        "contentMapperOptionDiagnostics",
        inputs,
        WatchFilter::NonWatch,
    );
}

// Go: tsc_test.go:4880 TestTscContentMapperFailures
#[test]
fn tsc_content_mapper_failures() {
    let fail_mapper_package_json = dedent(
        r#"
    {
        "name": "fail",
        "version": "1.0.0",
        "typescript": { "contentMapper": { "exec": ["failing-mapper"] } }
    }"#,
    );
    let fail_mapper_ts_config = dedent(
        r#"
    {
        "contentMappers": [
            { "package": "fail", "extensions": [".vue"] }
        ]
    }"#,
    );
    let inputs = vec![
        TscInput {
            sub_scenario: "initialization failure reports one project error".to_string(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
                {
                    "contentMappers": [
                        { "package": "missing", "extensions": [".vue"] }
                    ]
                }"#),
                "/home/src/workspaces/project/index.ts" => dedent(r#"
                    import "./a.vue";
                    import "./b.vue";
                    import "./c.vue";
                    import "./d.vue";
                    import "./e.vue";
                    import "./f.vue";"#),
                "/home/src/workspaces/project/a.vue" => "<template>a</template>",
                "/home/src/workspaces/project/b.vue" => "<template>b</template>",
                "/home/src/workspaces/project/c.vue" => "<template>c</template>",
                "/home/src/workspaces/project/d.vue" => "<template>d</template>",
                "/home/src/workspaces/project/e.vue" => "<template>e</template>",
                "/home/src/workspaces/project/f.vue" => "<template>f</template>",
                "/home/src/workspaces/project/node_modules/missing/package.json" => dedent(r#"
                {
                    "name": "missing",
                    "version": "1.0.0",
                    "typescript": { "contentMapper": { "exec": ["missing-mapper"] } }
                }"#),
            },
            command_line_args: argv(&["--runExternalCode", "--singleThreaded"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "transform failure reports a per-file error".to_string(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.json" => fail_mapper_ts_config.clone(),
                "/home/src/workspaces/project/index.ts" => r#"import "./app.vue";"#,
                "/home/src/workspaces/project/app.vue" => "<template>hi</template>",
                "/home/src/workspaces/project/node_modules/fail/package.json" =>
                    fail_mapper_package_json.clone(),
            },
            command_line_args: argv(&["--runExternalCode"]),
            ..Default::default()
        },
        TscInput {
            sub_scenario: "mapper is disabled after repeated failures".to_string(),
            files: files! {
                "/home/src/workspaces/project/tsconfig.json" => fail_mapper_ts_config,
                "/home/src/workspaces/project/index.ts" => dedent(r#"
                    import "./a.vue";
                    import "./b.vue";
                    import "./c.vue";
                    import "./d.vue";
                    import "./e.vue";
                    import "./f.vue";
                    import "./g.vue";"#),
                "/home/src/workspaces/project/a.vue" => "<template>a</template>",
                "/home/src/workspaces/project/b.vue" => "<template>b</template>",
                "/home/src/workspaces/project/c.vue" => "<template>c</template>",
                "/home/src/workspaces/project/d.vue" => "<template>d</template>",
                "/home/src/workspaces/project/e.vue" => "<template>e</template>",
                "/home/src/workspaces/project/f.vue" => "<template>f</template>",
                "/home/src/workspaces/project/g.vue" => "<template>g</template>",
                "/home/src/workspaces/project/node_modules/fail/package.json" =>
                    fail_mapper_package_json,
            },
            // --singleThreaded makes file loading order deterministic so the same files exceed the failure
            // threshold on every run.
            command_line_args: argv(&["--runExternalCode", "--singleThreaded"]),
            ..Default::default()
        },
    ];
    run_tsc_inputs("contentMapperFailures", inputs, WatchFilter::NonWatch);
}

// Go: tsc_test.go:4967 TestTscContentMapperSynthesized
#[test]
fn tsc_content_mapper_synthesized() {
    let inputs = vec![TscInput {
        sub_scenario: "diagnostics in synthesized code render on the virtual text".to_string(),
        files: files! {
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
            {
                "contentMappers": [
                    { "package": "synth", "extensions": [".vue"] }
                ]
            }"#),
            "/home/src/workspaces/project/index.ts" => r#"import "./app.vue";"#,
            "/home/src/workspaces/project/app.vue" => dedent(r"
                <template>
                    <Widget />
                </template>"),
            "/home/src/workspaces/project/node_modules/synth/package.json" => dedent(r#"
            {
                "name": "synth",
                "version": "1.0.0",
                "typescript": { "contentMapper": { "exec": ["synthesizing-mapper"] } }
            }"#),
        },
        command_line_args: argv(&["--runExternalCode"]),
        ..Default::default()
    }];
    run_tsc_inputs("contentMapperSynthesized", inputs, WatchFilter::NonWatch);
}
