// L5-typecheck
// ========================================================
import {equals, filter, flatten, includes, map, intersection, zipWith, reduce, all} from 'ramda';
import {
    isAppExp,
    isBoolExp,
    isDefineExp,
    isIfExp,
    isLetrecExp,
    isLetExp,
    isNumExp,
    isPrimOp,
    isProcExp,
    isProgram,
    isStrExp,
    isVarRef,
    unparse,
    parseL51,
    AppExp,
    BoolExp,
    DefineExp,
    Exp,
    IfExp,
    LetrecExp,
    LetExp,
    NumExp,
    SetExp,
    LitExp,
    Parsed,
    PrimOp,
    ProcExp,
    Program,
    StrExp,
    isSetExp,
    isLitExp,
    isDefineTypeExp,
    isTypeCaseExp,
    DefineTypeExp,
    TypeCaseExp,
    CaseExp,
    makeBoolExp,
    parseL51CExp,
    makeSetExp,
    parseSExp, VarDecl
} from "./L5-ast";
import {applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv} from "./TEnv";
import {
    isProcTExp,
    makeBoolTExp,
    makeNumTExp,
    makeProcTExp,
    makeStrTExp,
    makeVoidTExp,
    parseTE,
    unparseTExp,
    Record,
    BoolTExp,
    NumTExp,
    StrTExp,
    TExp,
    VoidTExp,
    UserDefinedTExp,
    isUserDefinedTExp,
    UDTExp,
    isNumTExp,
    isBoolTExp,
    isStrTExp,
    isVoidTExp,
    isRecord,
    ProcTExp,
    makeUserDefinedNameTExp,
    Field,
    makeAnyTExp,
    isAnyTExp,
    isUserDefinedNameTExp,
    makeTVar,
    isEmptyTVar, isCompoundTExp, parseTExp, makePairTExp, makeClosuerTExp, makeSymbolTExp
} from "./TExp";
import {isEmpty, allT, first, rest, cons} from '../shared/list';
import {
    Result,
    makeFailure,
    bind,
    makeOk,
    zipWithResult,
    mapv,
    mapResult,
    isFailure,
    either,
    isOk
} from '../shared/result';
import {
    isClosure, isCompoundSExp,
    isEmptySExp,
    isSymbolSExp,
    makeClosure, makeCompoundSExp,
    makeEmptySExp,
    makeSymbolSExp, SExpValue,
    valueToString
} from "./L5-value";
import * as Pred from '../shared/type-predicates';

// L51
export const getTypeDefinitions = (p: Program): UserDefinedTExp[] => {
    const iter = (head: Exp, tail: Exp[]): UserDefinedTExp[] =>
        isEmpty(tail) && isDefineTypeExp(head) ? [head.udType] :
            isEmpty(tail) ? [] :
                isDefineTypeExp(head) ? cons(head.udType, iter(first(tail), rest(tail))) :
                    iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getDefinitions = (p: Program): DefineExp[] => {
    const iter = (head: Exp, tail: Exp[]): DefineExp[] =>
        isEmpty(tail) && isDefineExp(head) ? [head] :
            isEmpty(tail) ? [] :
                isDefineExp(head) ? cons(head, iter(first(tail), rest(tail))) :
                    iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getRecords = (p: Program): Record[] =>
    flatten(map((ud: UserDefinedTExp) => ud.records, getTypeDefinitions(p)));

// L51
export const getItemByName = <T extends { typeName: string }>(typeName: string, items: T[]): Result<T> =>
    isEmpty(items) ? makeFailure(`${typeName} not found`) :
        first(items).typeName === typeName ? makeOk(first(items)) :
            getItemByName(typeName, rest(items));

// L51
export const getUserDefinedTypeByName = (typeName: string, p: Program): Result<UserDefinedTExp> =>
    getItemByName(typeName, getTypeDefinitions(p));

// L51
export const getRecordByName = (typeName: string, p: Program): Result<Record> =>
    getItemByName(typeName, getRecords(p));

// L51
// Given the name of record, return the list of UD Types that contain this record as a case.
export const getRecordParents = (typeName: string, p: Program): UserDefinedTExp[] =>
    filter((ud: UserDefinedTExp): boolean => map((rec: Record) => rec.typeName, ud.records).includes(typeName),
        getTypeDefinitions(p));


// L51
// Given a user defined type name, return the Record or UD Type which it names.
// (Note: TS fails to type check either in this case)
export const getTypeByName = (typeName: string, p: Program): Result<UDTExp> => {
    const ud = getUserDefinedTypeByName(typeName, p);
    if (isFailure(ud)) {
        return getRecordByName(typeName, p);
    } else {
        return ud;
    }
}

// TODO L51
// Is te1 a subtype of te2?
const isSubType = (te1: TExp, te2: TExp, p: Program): boolean =>
{    if (isAnyTExp(te2))
    return true;
else if (isUserDefinedNameTExp(te1) && isUserDefinedNameTExp(te2)  || isUserDefinedNameTExp(te1) && isUserDefinedTExp(te2)){
    const te2UDTexp: Result<UserDefinedTExp> = getUserDefinedTypeByName(te2.typeName , p);
    if(isOk(te2UDTexp))
        return isOk(te2UDTexp) ? (getRecordParents(te1.typeName , p).includes(te2UDTexp.value)) : false;
    else return false;
}
else return false;
}


// TODO L51: Change this definition to account for user defined types
// Purpose: Check that the computed type te1 can be accepted as an instance of te2
// test that te1 is either the same as te2 or more specific
// Deal with case of user defined type names
// Exp is only passed for documentation purposes.
// p is passed to provide the context of all user defined types
export const checkEqualType = (te1: TExp, te2: TExp, exp: Exp, p: Program): Result<TExp> =>
    equals(te1, te2) ? makeOk(te2) :
        isSubType(te1 , te2 ,p) ? makeOk(te2):
            makeFailure(`Incompatible types: ${te1} and ${te2} in ${exp}`);


// L51
// Return te and its parents in type hierarchy to compute type cover
// Return type names (not their definition)
export const getParentsType = (te: TExp, p: Program): TExp[] =>
    (isNumTExp(te) || isBoolTExp(te) || isStrTExp(te) || isVoidTExp(te) || isAnyTExp(te)) ? [te] :
        isProcTExp(te) ? [te] :
            isUserDefinedTExp(te) ? [te] :
                isRecord(te) ? getParentsType(makeUserDefinedNameTExp(te.typeName), p) :
                    isUserDefinedNameTExp(te) ?
                        either(getUserDefinedTypeByName(te.typeName, p),
                            (ud: UserDefinedTExp) => [makeUserDefinedNameTExp(ud.typeName)],
                            (_) => either(getRecordByName(te.typeName, p),
                                (rec: Record) => cons(makeUserDefinedNameTExp(rec.typeName),
                                    map((ud) => makeUserDefinedNameTExp(ud.typeName),
                                        getRecordParents(rec.typeName, p))),
                                (_) => [])) :
                        [];

// L51
// Get the list of types that cover all ts in types.
export const coverTypes = (types: TExp[], p: Program): TExp[] =>
    // [[p11, p12], [p21], [p31, p32]] --> types in intersection of all lists
{ const parentsList : TExp[][] = map((t) => getParentsType(t,p), types);
    return reduce<TExp[], TExp[]>(intersection, first(parentsList), rest(parentsList));
}

// Return the most specific in a list of TExps
// For example given UD(R1, R2):
// - mostSpecificType([R1, R2, UD]) = R1 (choses first out of record level)
// - mostSpecificType([R1, number]) = number
export const mostSpecificType = (types: TExp[], p: Program): TExp =>
    reduce((min: TExp, element: TExp) => isSubType(element, min, p) ? element : min,
        makeAnyTExp(),
        types);

// L51
// Check that all t in types can be covered by a single parent type (not by 'any')
// Return most specific parent
export const checkCoverType = (types: TExp[], p: Program): Result<TExp> => {
    const cover = coverTypes(types, p);
    return isEmpty(cover) ? makeFailure(`No type found to cover ${map((t) => JSON.stringify(unparseTExp(t), null, 2), types).join(" ")}`) :
        makeOk(mostSpecificType(cover, p));
}


// Compute the initial TEnv given user defined types
// =================================================
// TODO L51
// Construct type environment for the user-defined type induced functions
// Type constructor for all records
// Type predicate for all records
// Type predicate for all user-defined-types
// All globally defined variables (with define)

// TODO: Define here auxiliary functions for TEnv computation
const getArgsTypes = (args : Field[]) : TExp[] => {
    let res : TExp[] = [];
    for (let i = 0; i < args.length; i++){
        res.push(args[i].te);
    }
    return res;
}
// TOODO L51
// Initialize TEnv with:
// * Type of global variables (define expressions at top level of p)
// * Type of implicitly defined procedures for user defined types (define-type expressions in p)
export const initTEnv = (p: Program): TEnv => {  const typeDef: UserDefinedTExp[] = getTypeDefinitions(p)
    let types : TExp[] = [];
    let exps : string[] = [];
    let records = getRecords(p);
    let uds = getTypeDefinitions(p);
    let defs = getDefinitions(p);
    for (let i = 0; i < records.length ; i++){
        exps.push(records[i].typeName);
        exps.push("make-" + records[i].typeName);
        exps.push(records[i].typeName + "?");
        types.push(records[i]);
        types.push(makeProcTExp(getArgsTypes(records[i].fields), makeUserDefinedNameTExp(records[i].typeName)));
        types.push(makeProcTExp([makeAnyTExp()] , makeBoolTExp()));
    }

    for (let i = 0; i < uds.length ; i++){
        exps.push(uds[i].typeName);
        exps.push(uds[i].typeName + "?");
        types.push(uds[i]);
        types.push(makeProcTExp([makeAnyTExp()] , makeBoolTExp()));
    }

    for (let i = 0; i < defs.length ; i++){
        exps.push(defs[i].var.var);
        types.push(defs[i].var.texp);
    }

    return makeExtendTEnv(exps,types,makeEmptyTEnv());
}



// Verify that user defined types and type-case expressions are semantically correct
// =================================================================================
// TODO L51

export const getAllRecordsFilteredByName: ((rec:Record , records:Record[])=> Record[]) = (rec:Record, records:Record[]) => filter ((currRec:Record) => currRec.typeName ===  rec.typeName  , records);
export const isSame: ((records:Record[], first:Record) => boolean) = (records:Record[] , first:Record) => reduce((acc , curr)=> (acc &&  equals(curr.fields ,first.fields)),true,records);
export const checkUserDefinedTypes = (p: Program): Result<true> =>{
    const UDtypes:UserDefinedTExp[] = getTypeDefinitions(p);
    const records:Record[] = getRecords(p);
    //condition 1
    const constraint1: boolean = reduce (  (acc:boolean ,curr:Record) => curr && isSame( getAllRecordsFilteredByName(curr , records) , curr)  , true , records)

    //condition 2
    const constraint2: boolean = reduce ( (acc: boolean, curr: UserDefinedTExp) =>  acc && isGoodUDType(curr) , true ,UDtypes);

    return (constraint1 && constraint2) ?makeOk(true) : makeFailure("one of the constraints is false");
}


export const isRecursive: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => UDtype.records.some((rec:Record) => rec.fields.some((f:Field) => equals(f.te , makeUserDefinedNameTExp(UDtype.typeName)) ))
export const isBaseCase: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => UDtype.records.some((rec:Record) => rec.fields.every((f:Field) => !equals(f.te , makeUserDefinedNameTExp(UDtype.typeName)) ))
export const isGoodUDType: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => !isRecursive(UDtype) || (isRecursive(UDtype) && isBaseCase(UDtype));
// TODO L51
const checkTypeCase = (tc: TypeCaseExp, p: Program): Result<true> => {
    let resUd = getUserDefinedTypeByName(tc.typeName, p);
    if (isOk(resUd)) {
        if (tc.cases.length != resUd.value.records.length) {
            const names1 = map((x) => x.typeName, tc.cases);
            const names2 = map((x) => x.typeName, resUd.value.records);
            const intersection = names1.filter(name => names2.includes(name));
            if (intersection.length != tc.cases.length) {
                return makeFailure("check type case failed 1");
            }
        }
        let ud = resUd.value;
        for (let i = 0; i < ud.records.length; i++) {
            const fields1 = ud.records[i].fields;
            let arr = filter((x) => x.typeName == ud.records[i].typeName, tc.cases)
            if (arr.length != 1) {
                return makeFailure("check type case failed 2");
            }
            let varDecls = arr[0].varDecls; // 0 because length must be 1
            if (varDecls.length != fields1.length) {
                return makeFailure("check type case failed 3");
            }
        }
        return makeOk(true);
    }
    return makeFailure("check type case failed 4");
}

// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L51typeofProgram = (concreteExp: string): Result<string> =>
    bind(parseL51(concreteExp), (p: Program) =>
        bind(typeofExp(p, initTEnv(p), p), unparseTExp));

// For tests on a single expression - wrap the expression in a program
export const L51typeof = (concreteExp: string): Result<string> =>
    L51typeofProgram(`(L51 ${concreteExp})`);

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv, p: Program): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
        isBoolExp(exp) ? makeOk(typeofBool(exp)) :
            isStrExp(exp) ? makeOk(typeofStr(exp)) :
                isPrimOp(exp) ? typeofPrim(exp) :
                    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
                        isIfExp(exp) ? typeofIf(exp, tenv, p) :
                            isProcExp(exp) ? typeofProc(exp, tenv, p) :
                                isAppExp(exp) ? typeofApp(exp, tenv, p) :
                                    isLetExp(exp) ? typeofLet(exp, tenv, p) :
                                        isLetrecExp(exp) ? typeofLetrec(exp, tenv, p) :
                                            isDefineExp(exp) ? typeofDefine(exp, tenv, p) :
                                                isProgram(exp) ? typeofProgram(exp, tenv, p) :
                                                    isSetExp(exp) ? typeofSet(exp, tenv, p) :
                                                        isLitExp(exp) ? typeofLit(exp, tenv, p) :
                                                            isDefineTypeExp(exp) ? typeofDefineType(exp, tenv, p) :
                                                                isTypeCaseExp(exp) ? typeofTypeCase(exp, tenv, p) :
                                                                    makeFailure(`Unknown type: ${JSON.stringify(exp, null, 2)}`);

// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: Exp[], tenv: TEnv, p: Program): Result<TExp> =>
    isEmpty(rest(exps)) ? typeofExp(first(exps), tenv, p) :
        bind(typeofExp(first(exps), tenv, p), _ => typeofExps(rest(exps), tenv, p));

// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

// number | boolean | string | PrimOp | Closure | SymbolSExp | EmptySExp | CompoundSExp | void;


// L51 Todo: cons, car, cdr, list
export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
        (p.op === '-') ? numOpTExp :
            (p.op === '*') ? numOpTExp :
                (p.op === '/') ? numOpTExp :
                    (p.op === 'and') ? boolOpTExp :
                        (p.op === 'or') ? boolOpTExp :
                            (p.op === '>') ? numCompTExp :
                                (p.op === '<') ? numCompTExp :
                                    (p.op === '=') ? numCompTExp :
                                        // Important to use a different signature for each op with a TVar to avoid capture
                                        (p.op === 'number?') ? parseTE('(T -> boolean)') :
                                            (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
                                                (p.op === 'string?') ? parseTE('(T -> boolean)') :
                                                    (p.op === 'list?') ? parseTE('(T -> boolean)') :
                                                        (p.op === 'pair?') ? parseTE('(T -> boolean)') :
                                                            (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
                                                                (p.op === 'not') ? parseTE('(boolean -> boolean)') :
                                                                    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
                                                                        (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
                                                                            (p.op === 'display') ? parseTE('(T -> void)') :
                                                                                (p.op === 'newline') ? parseTE('(Empty -> void)') :
                                                                                    makeFailure(`Primitive not yet implemented: ${p.op}`);

// TODO L51
// Change this definition to account for possibility of subtype expressions between thenTE and altTE
//
// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1


export const typeofIf = (ifExp: IfExp, tenv: TEnv, p: Program): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv, p);
    const thenTE = typeofExp(ifExp.then, tenv, p);
    const altTE = typeofExp(ifExp.alt, tenv, p);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp, p));   //check if test is boolean predicate
    const constraint2 = bind(thenTE, (thenTE: TExp) =>                                              //check if then is subtype of alt
        bind(altTE, (altTE: TExp) =>
            checkEqualType(thenTE, altTE, ifExp, p)));
    const constraint3 = bind(altTE, (altTE: TExp) =>                                                ////check if alt is subtype of then
        bind(thenTE, (thenTE: TExp) =>
            checkEqualType(altTE, thenTE, ifExp, p)));

    if(isOk(constraint2))
        return bind(constraint1, (_c1) => constraint2);
    else
        return bind(constraint1, (_c1) => constraint3);
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv, p: Program): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv, p), (body: TExp) =>
        checkEqualType(body, proc.returnTE, proc, p));
    return bind(constraint1, (returnTE: TExp) => makeOk(makeProcTExp(argsTEs, returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv, p: Program): Result<TExp> =>
    bind(typeofExp(app.rator, tenv, p), (ratorTE: TExp) => {
        if (!isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                bind(unparse(app), (exp: string) =>
                    makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv, p), (typeOfRand: TExp) =>
                checkEqualType(typeOfRand, trand, app, p)),
            app.rands, ratorTE.paramTEs);
        return mapv(constraints, _ => ratorTE.returnTE);
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv, p: Program): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv, p), (typeOfVal: TExp) =>
            checkEqualType(varTE, typeOfVal, exp, p)),
        varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv), p));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv, p: Program): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (!allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${JSON.stringify(exp, null, 2)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
        paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI, p), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) =>
        zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp, p), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody, p));
};

// TODO - write the true definition
// Purpose: compute the type of a define
// Typing rule:
//   (define (var : texp) val)
//   tenv-val = extend-tenv(var:texp; tenv)
// If   type<val>(tenv-val) = texp
// then type<(define (var : texp) val)>(tenv) = void
export const typeofDefine = (exp: DefineExp, tenv: TEnv, p: Program): Result<VoidTExp> => {
    const v = exp.var.var;
    const texp = exp.var.texp;
    const val = exp.val;
    const tenvVal = makeExtendTEnv([v], [texp], tenv);
    const constraint = typeofExp(val, tenvVal, p);
    return mapv(constraint, (_) => makeVoidTExp());
};

// Purpose: compute the type of a program
// Typing rule:
export const typeofProgram = (exp: Program, tenv: TEnv, p: Program): Result<TExp> =>
    typeofExps(exp.exps, tenv, p);

// TODO L51
// Write the typing rule for DefineType expressions
export const typeofDefineType = (exp: DefineTypeExp, _tenv: TEnv, _p: Program): Result<TExp> => {
    const udType:UserDefinedTExp = exp.udType;
    const records: Record[] = udType.records;
    const recordsNames: string[] = map ((rec:Record) => rec.typeName , records);
    const nEnv = makeExtendTEnv(recordsNames , records , _tenv);

    // const constraint1 =
    return makeOk(makeVoidTExp());
}

// TODO L51
// Typing rule:
//   (set! var val)
// Typing rule set!:
//   For every: type environment _Tenv,
//              variable reference _x1
//              expressions _e1 and
//              type expressions _S1:
//   If _Tenv |- _e1 : _S1 and
//      _Tenv |- _x1 : _S1
//   Then _Tenv |- (set! _x1 _e1) : void
export const typeofSet = (exp: SetExp, _tenv: TEnv, _p: Program): Result<TExp> => {
    const v = exp.var.var
    const v1 = exp.var
    const val = exp.val
    const valRes = typeofExp(val, _tenv, _p)

    if (isOk(valRes)) {
        const typeVal = valRes.value
        makeExtendTEnv([v], [typeVal], _tenv);
        return makeOk(makeVoidTExp())
    } else {
        return makeFailure(`Unknown literal type ${exp.val}`);
    }
}
// TODO L51
    export const typeofLit = (exp: LitExp, _tenv: TEnv, _p: Program): Result<TExp> => {
    const val:SExpValue = exp.val;
        return Pred.isNumber(val) ?  makeOk(makeNumTExp()) :
            Pred.isBoolean(val) ? makeOk(makeBoolTExp()) :
                Pred.isString(val) ? makeOk(makeStrTExp()) :
                    isPrimOp(val) ? typeofPrim(val) :
                        isSymbolSExp(val) ? makeOk(makeSymbolTExp()) :
                            makeOk(makeVoidTExp());
    }


// TODO: L51
// Purpose: compute the type of a type-case
// Typing rule:
// For all user-defined-type id
//         with component records record_1 ... record_n
//         with fields (field_ij) (i in [1...n], j in [1..R_i])
//         val CExp
//         body_i for i in [1..n] sequences of CExp
//   ( type-case id val (record_1 (field_11 ... field_1r1) body_1)...  )
//  TODO
const getCaseNames:(cas:CaseExp) => string[] = (cas:CaseExp) => map((vd: VarDecl) => vd.var ,  cas.varDecls);

const getCaseTypes:(cas:CaseExp , p:Program) => TExp[] = (cas:CaseExp ,  p:Program) =>   {
    const rec:Result<Record> = getRecordByName(cas.typeName , p);
    return isOk(rec) ? map ((fi:Field) => fi.te , rec.value.fields) : [];
}
export const typeofTypeCase = (exp: TypeCaseExp, tenv: TEnv, p: Program): Result<TExp> => {
        const constraint1:Result<true> = checkTypeCase(exp ,p );


        const checkCorretTypeCase: (exp: TypeCaseExp) => Result<TExp> = (exp: TypeCaseExp) => {
            const cases:CaseExp[] = exp.cases;
            const newEnv = makeExtendTEnv(getCaseNames(cases[0]),getCaseTypes(cases[0] , p),tenv)
            const firstCaseType = typeofExps(cases[0].body, newEnv ,p);
            const constraint2 = cases.every( (cas:CaseExp) => {
                const newT = typeofExps(cas.body,makeExtendTEnv(getCaseNames(cas),getCaseTypes(cas , p),tenv),p)
                return equals (typeofExps(cas.body,makeExtendTEnv(getCaseNames(cas),getCaseTypes(cas , p),tenv),p) , firstCaseType )
            } )
            return constraint2 ? firstCaseType : makeFailure("case types are not equal");
        }

        return bind (constraint1 , (constraint1r:boolean) => checkCorretTypeCase(exp))
    }
