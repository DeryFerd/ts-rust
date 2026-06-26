export interface User {
    id: number;
    name: string;
}

export const makeUser = (user: User): User => user;
