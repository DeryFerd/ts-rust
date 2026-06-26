type Props = {
    title: string;
    values: readonly string[];
};

export const View = ({ title, values }: Props) => (
    <main>
        <h1>{title}</h1>
        <ul>{values.map((value) => <li>{value}</li>)}</ul>
    </main>
);
