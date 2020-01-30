# Rast

Simple experimental implementation of purely linear logic, extended
with temporal and ergometric types as well as constraints over natural
numbers in Presburger arithmetic.

This is a version of recent ICFP, LICS, and arXiv papers, see

- [Parallel Complexity Analysis with Temporal Session Types](http://www.cs.cmu.edu/~fp/papers/icfp18.pdf)
- [Work Analysis with Resource-Aware Session Types](http://www.cs.cmu.edu/~fp/papers/lics18.pdf)
- [Session Types with Arithmetic Refinements and Their Application to Work Analysis](https://arxiv.org/abs/2001.04439) 

Authors:

- Ankush Das
- Frank Pfenning

## Building rast

Requires Standard ML, mlton to build binaries

For building a binary (with mlton):

```
% cd src
% make rast
% ./rast ../examples/trie-work.rast
% ./rast -h
```

or for interactive top level (with SML/NJ):

```
% sml
- CM.make "sources.cm";
- Top.rast "../examples/trie-work.rast";

% make clean
```

For regression testing:

```
% make rast-test
% ./rast-test ../*/*.rast
% ./rast-test -h
```

## Examples

A postfix `-work` indicates use of ergometric types to capture work

- `arith*.rast`      - some binary and unary arithmetic on natural numbers
- `intctr.rast`      - integer counter
- `linlam*.rast`     - various versions of linear lambda-calculus
- `list-work.rast`   - processes on lists, characterizing work
- `primes.rast`      - prime sieve
- `seg-work.rast`    - list segments, characterizing work
- `ternary.rast`     - balanced ternary numbers
- `theorems.rast`    - simple arithmetic metatheorems and proofs
- `trie-work.rast`   - multisets of binary numbers, as a trie

## Options to ./rast

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

--equality=subsumerefl  type equality uses subsumption and reflexivity (default)
--equality=subsume      use only subsumption
--equality=refl         use only reflexivity
```

Currently, the implementation cannot perform both time reconstruction
so with `--syntax=implicit` we must have `--time=none`

## Grammar 

In arithmetic expressions, operator precedence is as follows, where
unary minus `-` has highest precedent

```text
'*' > '+' '-' > '=' '<' '<=' '=' '<>' '>=' '>' > '~' > '/\' > '\/' > '=>'
```

Left associative are `*` `+` `-`

Right associative are `/\` `\/` `=>`

Not associative are `<` `<=` `=` `>=` `>`

Note: the order of branches must match the order of the alternatives
in the external or internal choice type

### Comment syntax

```text
% ... \n
(* ... *)  (multiline, properly nested)
```

### Syntax

```text
<id_start> = [a-zA-Z_$?!']
<id> = <id_start> (<id_start> | [0-9])*
<nat> = ([0-9])*
<unop> = -
<binop> = * | + | -
<arith> = <nat> | <id> | <unop> <arith> | <arith> <binop> <arith> | (<arith>)
<rel> = > | >= | = | <> | <= | <
<prop> = <arith> <rel> <arith>
       | ~ <prop> | <prop> /\ <prop> | <prop> \/ <prop> | <prop> => <prop>

<idx> ::= { <arith> }

<con> ::= { <prop> }

<type> ::= 1                    % Unit
         | + { <choices> }      % Internal choice
         | & { <choices> }      % External choice
         | <type> * <type>      % Tensor
         | <type> -o <type>     % Lolli
         | ( [<idx>] ) <type>   % Next
         | ` <type>             % Next, from cost model
         | [ ] <type>           % Always
         | < > <type>           % Eventually
         | | [<idx>] > <type>   % Provide potential <arith> (default: 1)
         | < [<idx>] | <type>   % Obtain potential <arith> (default: 1)
         | <id> <idx_seq>       % Type name
         | ? <con>. <type>      % Provider send 'proof' of <prop>
         | ! <con>. <type>      % Provider receives 'proof' of <prop>
         | ? <id>. <type>       % Existential type
         | ! <id>. <type>       % Universal type
         | ( <type> )           % Parentheses

<idx_seq> ::=  | <idx> <idx_seq>
<id_seq> ::=  | <id> <id_seq>

<choices> ::= <label> : <type>
            | <label> : <type>, <choices>

<turnstile> ::= |-              % zero potential
              | | <idx> -       % with potential <idx>

<exp> ::= <id> <- <id> <idx_seq> <id_seq> ; <exp>     % spawn
        | <id> <- <id> <idx_seq> <id_seq>             % tail call
        | <id> <-> <id>                               % forward
        | <id>.<label> ; <exp>                        % send label 
        | case <id> ( <branches> )                    % branch on label received
        | close <id>                                  % close channel
        | wait <id> ; <exp>                           % wait for channel to be closed
        | send <id> <id> ; <exp>                      % send channel
        | <id> <- recv <id> ; <exp>                   % receive channel
        | send <id> { <arith> } ; <exp>               % send natural number
        | { <id> } <- recv <id> ; <exp>               % receive natural number
        
        | assert <id> <con> ; <exp>                   % assert constraints
        | assume <id> <con> ; <exp>                   % assume constraint
        | impossible                                  % constraints are contradictory

        | ( <exp> )

        | delay [<idx>] ; <exp>                       % delay by <idx> clock ticks
        | tick ; <exp>                                % one clock tick in cost model
        | when <id> ; <exp>                           % wait for 'now' message
        | now <id> ; <exp>                            % send 'now' message

        | work [<idx>] ; <exp>                        % perform <idx> units of work
        | get <id> [<idx>] ; <exp>                    % receive <idx> potential
        | pay <id> [<idx>] ; <exp>                    % send <idx> potential

<branches> ::= <label> => <exp>
             | <label> => <exp> | <branches>

<var> ::= _ | <id>

<var_seq> ::=
           | { <var> } <var_seq>
           | { <var> | <prop> } <var_seq>

<ctx> ::= . | ( <id> : <type> ) <ctx>

<decl> ::= type <id> <var_seq> = <type>
         | eqtype <id> <idx_seq> = <id> <idx_seq>
         | decl <id> <var_seq> : <ctx> <turnstile> ( <id> : <type> )
         | proc <id> <- <id> <var_seq> <id_seq> = <exp>
         | exec <id>

<outcome> ::= error
            | success
            | approx success
            | approx error

<pragma> ::= #options <command line options>\n
           | #test <outcome>\n

<prog> ::= <pragma>* <decl>*
```

