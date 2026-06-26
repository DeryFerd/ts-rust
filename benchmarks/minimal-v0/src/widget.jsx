export const Widget = ({ active }) => (
    <button aria-pressed={active}>{active ? "on" : "off"}</button>
);
