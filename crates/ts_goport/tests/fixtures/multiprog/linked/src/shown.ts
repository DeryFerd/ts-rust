import { first } from "./shelved";

// The test links node_modules/shelf to packages/shelf. This file does not
// import "shelf", so the module specifier of `Book` in the type of `second`
// is "shelf" only with the symlink cache of this program. The files a.ts to
// c.ts put this file after the files that the other programs print.
export const second = first;
