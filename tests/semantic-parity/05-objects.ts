export {};

interface Options {
    readonly enabled: boolean;
    label?: string;
}

const options: Options = { enabled: true, extra: 1 };
options.enabled = false;
const required: { label: string } = options;
