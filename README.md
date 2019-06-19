# SubSingleton

Simple experimental implementation of subsingleton logic, extended
with temporal and ergometric types as well as constraints over natural
numbers in Presburger arithmetic and termination checking.

This is the subsingleton version of recent ICFP and LICS papers, see

- [Parallel Complexity Analysis with Temporal Session Types](http://www.cs.cmu.edu/~fp/papers/icfp18.pdf)
- [Work Analysis with Resource-Aware Session Types](http://www.cs.cmu.edu/~fp/papers/lics18.pdf)

Authors:

- Ankush Das
- Farzaneh Derakhshan
- Frank Pfenning

## Building ss

Requires Standard ML, mlton to build binaries

For building a binary (with mlton):

```
% cd src
% make ss
% ./ss ../examples/icfp18/sec7i.ss
% ./ss -h
```

or for interactive top level (with SML/NJ):

```
% sml
- CM.make "sources.cm";
- Top.ss "../examples/icfp18/sec7i.ss";

% make clean
```

For regression testing:

```
% make ss-test
% ./ss-test ../tests/*/*.ss ../examples/*/*.ss
% ./ss-test -h
```

## Examples

- `icfp18/*.ss`    - mostly temporal, see http://www.cs.cmu.edu/~fp/papers/icfp18.pdf
- `lics18/*.ss`    - mostly ergometric, see http://www.cs.cmu.edu/~fp/papers/lics18.pdf
- `binarith/*.ss`  - binary arithmetic
- `modarith/*.ss`  - modular binary arithmetic
- `turing/*.ss`    - some primitive recursive functions as Turing machines

## Tests

- `types/*.ss`       - testing the type checker
- `termination/*.ss` - testing the termination checker
- `ztests/*/*.ss`  - tests that fail due to various restriction and sources of incompleteness

## Options to ./ss

```
-q quiet   (verbosity = 0) 
-v verbose (verbosity = 1)
-d debug   (verbosity = 2)
-h help

--time=none      only explicit delays/work (default)
--time=free      both sends and receives are free
--time=recv      every receive costs one clock tick
--time=send      every send costs one clock tick 
--time=recvsend  every receive and send costs one clock tick

--work=none      only explicit delays/work (default)
--work=free      both sends and receives are free
--work=recv      every receive costs one unit of work
--work=send      every send costs one unit of work
--work=recvsend  every receive and send costs one unit of work

--syntax=implicit  will perform time or work reconstruction (default)
--syntax=explicit  will not perform time or work reconstruction

--terminate=none   perform no termination checking (default)
--terminate=equi   will perform termination checking on equirecursive code
--terminate=iso    will perform termination checking on isorecursive code
```

Currently, the implementation cannot perform both time
and work reconstruction on the same source: with `--syntax=implicit`
either time or work must be `none`

## Grammar 

typed cut `{<type>}` or untyped cut `||`
are right associative and bind more
tightly than `;`

```
   L.a ; L.b ; f || R.c ; g
=> L.a ; (L.b ; (f || (R.c ; g)))

   L.a ; L.b ; <-> {A} R.c ; g
=> L.a ; (L.b ; (<-> {A} (R.c ; g)))
```

In arithmetic expressions, operator precedence is as follows.

```
* > + = -
```

All operators are left associative.

Note: right now, the order of branches must match
the order of the alternatives in the external or
internal choice type

A typed cut may be annotated with the
potential of the process on the left.  For example
`f {|{3}- bits} g`
indicates `3` units of potential should be passed to f.

### Comment syntax

```
% ... \n
\(* ... *\)  (multiline, properly nested)
```

### Syntax

```
<id_start> = [a-zA-Z_$?!\']
<id> = <id_start> (<id_start> | [0-9])*
<nat> = ([0-9])*
<binop> = + | - | *
<arith> = <nat> | <id> | <arith> <binop> <arith> | (<arith>)
<rel> = > | >= | = | <= | <
<prop> = <arith> <rel> <arith>

<idx> ::= { <arith> }

<con> ::= { <prop> }

<type> ::= 1
         | + { <choices> }
         | & { <choices> }
         | ( [<idx>] ) <type>   % Next
         | ` <type>             % Next, from cost model
         | [ ] <type>           % Always
         | < > <type>           % Eventually
         | | [<idx>] > <type>   % Provide potential <arith> (default: 1)
         | < [<idx>] | <type>   % Obtain potential <arith> (default: 1)
         | <id> <idx_seq>
         | ? <con>. <type>      % Provider send \'proof\' of <prop>
         | ! <con>. <type>      % Provider receives \'proof\' of <prop>

<idx_seq> ::=  | <idx> <idx_seq>

<choices> ::= <label> : <type>
            | <label> : <type>, <choices>

<type_opt> ::= <type>
             | .

<turnstile> ::= |-              % zero potential
              | | <idx> -       % with potential <arith>
<dir> ::= L | R
<sr>  ::= ! | ?

<exp> ::= <exp> [ [<turnstile>] <type> ] <exp> % typed cut
        | <exp> || <exp>        % spawn, left exp must be <id>
        | <->
        | <dir>.<label> ; <exp>
        | case<dir> ( <branches> )
        | closeR
        | waitL ; <exp>

        | <id> <idx_seq>
        | assert<dir> <con> ; <exp> 
        | impossible<dir> <con>
        | assume<dir> <con> ; <exp>
        | ( <exp> )

        | delay [<idx>] ; <exp> % delay by one clock tick
        | tick ; <exp>          % one clock tick in cost model
        | when<dir> ; <exp>     % wait for \'now\' message
        | now<dir> ; <exp>      % send \'now\' message

        | work [<idx>] ; <exp>          % spend one token
        | get<dir> [<idx>] ; <exp>      % receive one token
        | pay<dir> [<idx>] ; <exp>      % send one token

% not implemented
%        | unfold<sr><dir> ; <exp>  % send or receive unfold

<branches> ::= <label> => <exp>
             | <label> => <exp> | <branches>

<var> ::= _ | <id>

<var_seq> ::=
           | { <var> } <var_seq>
           | { <var> | <prop> } <var_seq>

<decl> ::= type <id> <var_seq> = <type>
         | eqtype <id> <idx_seq> = <id> <idx_seq>
         | proc <id> <var_seq> : [ <type_opt> <turnstile> ] <type>
         | proc <id> <var_seq> = <exp>
         | exec <id>

<outcome> ::= error
            | success

<pragma> ::= #options <command line option>\n
           | #test <outcome>\n

<prog> ::= <pragma>* <decl>*
```
