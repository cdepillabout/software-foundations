# software-foundations

This is from <https://softwarefoundations.cis.upenn.edu/>.

## Building

First get into the Nix shell:

```console
$ nix develop
```

Then, change into every one of the child directories and run.  For example, for
`volume-2-programming-language-foundations/`:

```console
$ cd volume-2-programming-language-foundations/
$ make
```

Then you should be able to open any `*.v` Coq file in `coqide`.  For example:

```console
$ coqide Sub.v
```

