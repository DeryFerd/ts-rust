// @effect-diagnostics-next-line globalDate:off this date is only for logs
export const skipped = new Date();
export const reported = new Date();
// @effect-diagnostics-next-line globalRandom:off globalDate:warning two rules and a reason
export const both = [new Date(), Math.random()];
// @effect-diagnostics-next-line globalFetch:off nothing to suppress here
export const unused = 1;
