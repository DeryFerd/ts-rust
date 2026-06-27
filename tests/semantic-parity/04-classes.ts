export {};

abstract class Base {
    abstract value: string;
    protected abstract read(): number;
}

class Derived extends Base {
    value = 1;
    private read() {
        return "wrong";
    }
}

new Base();
