// Go prints a type in at most 320 bytes: the first 317 bytes and "...".
// The type of `word` is a string literal type whose byte 317 is inside a
// 2-byte char.
export const word = "xэлементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў элементаў";

// The message prints the type of `word` with the same limit.
export const short: "x" = word;
