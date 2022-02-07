# coq-vyper
A compiler for a subset of [Vyper](https://github.com/vyperlang/vyper) (or [Fe](https://github.com/ethereum/fe)),
verified in Coq.
This is a work in progress.


## Status

The verified part transforms an AST to an AST. Neither parsing the source nor printing the resulting AST are not verified.

Currently the key restriction of the source language is that it only supports one type: *uint256*.

The target will eventually be YUL but as of now the target is a lower level language denoted L30.

## What Does it Do

Currently it certifiably correctly compiles all the language operators (on *uint256*) into a pseudo-assembly language L30. See also [NUANCES.md](NUANCES.md) for some fine details on language definition.

The compiler features a preliminary pass that decorates each function with a maximal possible call depth (or detects recursion). After that, it performs 4 passes:
1. resolves calls; processes assertions and augmented assignments; converts range loops to the less restrictive counted loops; makes AST more regular
2. folds constants
3. converts expressions to pseudo-assembly; replaces logical operators (*and*, *or*, *if*) with *if-else* statements
4. compiles checked arithmetic into code that uses only unchecked arithmetic modulo 2<sup>256</sup>

## Building

- install the prerequisites: *alex happy ghc coq*

- Coq 8.13 is required, 8.14 and later versions won't work until [https://github.com/coq/coq/issues/15067](this bug) is fixed.

- do the usual:

		./configure
		make
		
	The executable should be built at *haskell/coq-vyperc*

## Acknowledgments
This work is supported by Ethereum Foundation.

## Example

This Vyper code:

```python
def foo(f):
    a:uint256 = 10
    a += a ** 3 if f else 3 ** a
    return a
```

compiles into the following L30 code (in which 0x61726974686d65746963206572726f72 stands for "arithmetic error"):

```python
def foo/1:
    var1 = 0xa
    var2 = var1
    var3 = var0
    if var3:
        var3 = var1
        var4 = var3
        var5 = 0x285145f31ae515c447bb57
        var5 = $uint256_lt/2(var4, ...)
        if var5:
            var5 = 0x3
            var3 = $uint256_exp/2(var4, ...)
        else:
            var4 = 0x61726974686d65746963206572726f72
            raise var4
    else:
        var3 = var1
        var4 = 0xa1
        var5 = var3
        var6 = $uint256_lt/2(var4, ...)
        if var6:
            var4 = 0x61726974686d65746963206572726f72
            raise var4
        else:
            var4 = 0x3
            var3 = $uint256_exp/2(var4, ...)
    var4 = var2
    var5 = var3
    var5 = $uint256_add/2(var4, ...)
    var6 = var2
    var4 = $uint256_lt/2(var5, ...)
    if var4:
        var4 = 0x61726974686d65746963206572726f72
        raise var4
    else:
        var2 = var5
    var1 = var2
    var2 = var1
    return var2
    pass
```
