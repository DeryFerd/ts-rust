// The worker thread of one Node run (node.js `tsc`).

import { parentPort, workerData } from "node:worker_threads";
import { runRequest } from "./node-run.js";

parentPort.postMessage(runRequest(workerData));
