export {};

function format(value: string | number) {
    if (typeof value === "string") {
        value.toFixed();
    } else {
        value.toUpperCase();
    }
}

format(true);
