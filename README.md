# coq-vyper

This is a toy verified compiler for a small uint256-only language that is a dialect of [Vyper](https://github.com/vyperlang/vyper) or [Fe](https://github.com/ethereum/fe).
It is not very useful currently since it does not support even maps, but it demonstrates verified compilation of all the checked arithmetic and all the usual control flow into Yul.


# What Does it Do

The verified part transforms an AST to an AST. Neither parsing the source nor printing the resulting AST are verified.

The compiler features a preliminary pass that decorates each function with a maximal possible call depth (or detects recursion). After that, it performs 6 passes:
1. resolves calls; processes assertions and augmented assignments; converts range loops to the less restrictive counted loops; makes AST more regular
2. folds constants
3. converts expressions to pseudo-assembly; replaces logical operators (*and*, *or*, *if*) with *if-else* statements
4. compiles checked arithmetic into code that uses only unchecked arithmetic modulo 2<sup>256</sup>
5. changes loops into 0-based
6. translates everything into Yul (a significantly higher level language then the intermediate languages)

See also [NUANCES.md](NUANCES.md) for some fine details on language definition.

## Building

- install the prerequisites: *alex happy ghc coq*

- Coq 8.13 is required, 8.14 and later versions won't work until [https://github.com/coq/coq/issues/15067](this bug) is fixed.

- do the usual:

		./configure
		make
		
	The executable should be built at *haskell/coq-vyperc*

- I have often seen a bug in make (?) that requires running make twice.

## Acknowledgments
This work is supported by Ethereum Foundation.

## Example

This code:

```python
def foo(f):
    a:uint256 = 10
    a += a ** 3 if f else 3 ** a
    return a
```

compiles into the following Yul code (in which 0x61726974686d65746963206572726f72 stands for "arithmetic error"):

```javascript
function $foo($$var0:u256) -> $$result:u256
{
    let $$var1:u256
    let $$var2:u256
    let $$var3:u256
    let $$var4:u256
    let $$var5:u256
    let $$var6:u256
    $$var1 := 0xa:u256
    $$var2 := $$var1
    $$var3 := $$var0
    switch $$var3
    case 0x0:u256
    {
        $$var3 := $$var1
        $$var4 := 0xa1:u256
        $$var5 := $$var3
        $$var6 := lt($$var4, $$var5)
        switch $$var6
        case 0x0:u256
        {
            $$var4 := 0x3:u256
            $$var3 := exp($$var4, $$var5)
        }
        default
        {
            $$var4 := 0x61726974686d65746963206572726f72:u256
            mstore(0x0:u256, $$var4)
            revert(0x0:u256, 0x1:u256)
        }
    }
    default
    {
        $$var3 := $$var1
        $$var4 := $$var3
        $$var5 := 0x285145f31ae515c447bb57:u256
        $$var5 := lt($$var4, $$var5)
        switch $$var5
        case 0x0:u256
        {
            $$var4 := 0x61726974686d65746963206572726f72:u256
            mstore(0x0:u256, $$var4)
            revert(0x0:u256, 0x1:u256)
        }
        default
        {
            $$var5 := 0x3:u256
            $$var3 := exp($$var4, $$var5)
        }
    }
    $$var4 := $$var2
    $$var5 := $$var3
    $$var5 := add($$var4, $$var5)
    $$var6 := $$var2
    $$var4 := lt($$var5, $$var6)
    switch $$var4
    case 0x0:u256
    { $$var2 := $$var5 }
    default
    {
        $$var4 := 0x61726974686d65746963206572726f72:u256
        mstore(0x0:u256, $$var4)
        revert(0x0:u256, 0x1:u256)
    }
    $$var1 := $$var2
    $$var2 := $$var1
    $$result := $$var2
    leave
    $$result := 0x0:u256
}
```
