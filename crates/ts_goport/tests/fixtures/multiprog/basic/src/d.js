// @ts-check

/**
 * @typedef {object} Size
 * @property {number} width
 * @property {number} height
 */

/**
 * @param {Size} size
 * @returns {number}
 */
export function area(size) {
  return size.width * size.height;
}

/** @type {Size} */
export const unit = { width: 1, height: "1" };
