declare namespace Library {
    interface Events<T = number> {
        inherited: T;
        read(): T;
    }

    interface Emitter<T = number> extends Events<T> {}

    class Emitter<T = number> {
        ownClass: T;
    }

    interface Process extends Emitter {
        label: string;
        send?<K extends object>(message: K): K[keyof K];
    }
}

declare var service: Library.Process;
