import { Effect as E } from "effect";
import * as Effect from "effect/Effect";
import { Eff, EffectNs } from "./reexport.ts";
import { make, type Program } from "./make.ts";

E.succeed(1);
Effect.succeed(2);
Eff.succeed(3);
EffectNs.succeed(4);
make(5);
declare const program: Program;
program;
