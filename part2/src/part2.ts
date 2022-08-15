export const MISSING_KEY = '___MISSING_KEY___'
export const MISSING_TABLE_SERVICE = '___MISSING_TABLE_SERVICE___'

export type Table<T> = Readonly<Record<string, Readonly<T>>>

export type TableService<T> = {
    get(key: string): Promise<T>;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
}

// Q 2.1 (a)
export function makeTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>): TableService<T> {

    //
    // function updateMutableTable() {
    //     return sync().then((immtable) => {
    //             for (let key in immtable) {
    //                 mutableTable[key] = immtable[key]
    //             }
    //         }
    //     )
    // }
    //
    // function filterMutableTable(key: string) {
    //     return sync().then((immtable) => {
    //             for (let _key in immtable) {
    //                 if (_key !== key)
    //                     mutableTable[_key] = immtable[_key]
    //             }
    //         }
    //     )
    // }
    //
    // function createImmutableTable(mutableTable: Record<string, Readonly<T>>) {
    //     return Object.freeze(mutableTable)
    // }

    const curr_table = sync()
    return {
        get(key: string): Promise<T> {
            return new Promise(function (resolve, reject) {
                sync().then((table) => typeof table[key] !== 'undefined' ? resolve(table[key]) : reject(MISSING_KEY))
            })
        },
        set(key: string, val: T): Promise<void> {
            return new Promise<void>((resolve, reject) => {
                curr_table.then((table) => {
                    let mutableTable: Record<string, Readonly<T>> = table;
                    mutableTable[key] = val
                    sync(mutableTable).then(() => resolve()).catch(() => reject(MISSING_TABLE_SERVICE))
                }).catch(() => reject(MISSING_TABLE_SERVICE))
            })
        },
        delete(key: string): Promise<void> {
            return new Promise<void>((resolve, reject) => {
                curr_table.then((table) => {
                    let mutableTable: Record<string, Readonly<T>> = table;
                    if (key in mutableTable) delete mutableTable[key]
                    else reject(MISSING_KEY)
                    sync(mutableTable).then(() => resolve()).catch(() => reject(MISSING_TABLE_SERVICE))
                }).catch(() => reject(MISSING_TABLE_SERVICE))
            })
        },
    }
}


// Q 2.1 (b)
export function getAll<T>(store: TableService<T>, keys: string[]): Promise<T[]> {
    const promises = keys.map(key => store.get(key))
    return Promise.all(promises) //check reject missing key
}


// Q 2.2
export type Reference = { table: string, key: string }

export type TableServiceTable = Table<TableService<object>>

export function isReference<T>(obj: T | Reference): obj is Reference {
    return typeof obj === 'object' && 'table' in obj
}

export async function constructObjectFromTables(tables: TableServiceTable, ref: Reference): Promise<any> {
    async function deref(ref: Reference) {
        if (tables[ref.table] === undefined)
            return Promise.reject(MISSING_TABLE_SERVICE)
        const requiredTable = tables[ref.table]
        const valueToChange = await requiredTable.get(ref.key)
        try {
            let all = (Object.entries(valueToChange));
            for (let entry in all) {
                if (isReference(all[entry][1]))
                    all[entry][1] = await constructObjectFromTables(tables, all[entry][1]);
            }
            return Object.fromEntries(all);
        } catch {
            return Promise.reject(MISSING_KEY)
        }
    }

    return deref(ref)
}


// try{
//     let entries = (Object.entries(refVal));
//     for ( let entry in entries){
//         if ( isReference(entries[entry][1]))
//             entries[entry][1] = await func(tables , entries[entry][1]);
//     }
//     return Object.fromEntries(entries);
// }  catch{
//     Promise.reject(MISSING_KEY)
// }

// Q 2.3

export function lazyProduct<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        // TODO implement!
        let cr1: Iterator<T1> = g1();
        let cr2: Iterator<T2> = g2();
        let ir1: IteratorResult<T1> = cr1.next();
        let ir2: IteratorResult<T2> = cr2.next();
        while (!ir1.done) {

            while (!ir2.done) {
                yield [ir1.value, ir2.value]
                ir2 = cr2.next()
            }
            cr2 = g2();
            ir2 = cr2.next()
            ir1 = cr1.next()
        }
    }
}

export function lazyZip<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        // TODO implement!
        let cr1: Iterator<T1> = g1();
        let cr2: Iterator<T2> = g2();
        let ir1: IteratorResult<T1> = cr1.next();
        let ir2: IteratorResult<T2> = cr2.next();
        while (!ir1.done && !ir2.done) {
            yield [ir1.value, ir2.value]
            ir1 = cr1.next()
            ir2 = cr2.next()
        }
    }
}


// Q 2.4
export type ReactiveTableService<T> = {
    get(key: string): T;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
    subscribe(observer: (table: Table<T>) => void): void
}

export async function makeReactiveTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>, optimistic: boolean): Promise<ReactiveTableService<T>> {
    // optional initialization code
    let _table: Table<T> = await sync()
    let observers: Function[] = []


    const handleMutation = async (newTable: Table<T>) => {
        if (optimistic)
            observers.forEach(element => {
                element(newTable)
            });
        await sync(newTable).catch((err) => Promise.reject(err)).then(() => _table = newTable)
    }
    return {
        get(key: string): T {
            if (key in _table) {
                return _table[key]
            } else {
                throw MISSING_KEY
            }
        },
        set(key: string, val: T): Promise<void> {
            let newTable: Record<string, Readonly<T>> = Object.fromEntries(Object.entries(_table))
            newTable[key] = val
            return handleMutation(newTable).catch((err) => {
                observers.forEach(element => {
                    element(_table)
                })
                return Promise.reject(err)
            }).then(() => {
                if (!optimistic) {
                    observers.forEach(element => {
                        element(newTable)
                    })

                }
            })

        },
        delete(key: string): Promise<void> {
            let newTable: Record<string, Readonly<T>> = Object.fromEntries(Object.entries(_table))
            key in newTable ? delete newTable[key] : Promise.reject(MISSING_KEY)
            return handleMutation(newTable).catch((err) => {
                observers.forEach(element => {
                    element(_table)
                })
                return Promise.reject(err)
            })

                .then(() => {
                    if (!optimistic) {
                        observers.forEach(element => {
                            element(newTable)
                        })
                    }
                })
        },
        subscribe(observer: (table: Table<T>) => void): void {
            observers.push(observer)

        }

    }
}
