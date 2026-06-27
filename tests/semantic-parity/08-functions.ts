export {};

function parse(value: string): string;
function parse(value: number): number;
function parse(value: string | number) {
    return value;
}

parse(true);

let takesString: (value: string) => void;
const takesUnknown = (value: unknown) => value;
takesString = takesUnknown;
takesString = (value: number) => value;
