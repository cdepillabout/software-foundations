# software-foundations

This is from <https://softwarefoundations.cis.upenn.edu/>.

## Building

Each directory contains a different book of Software Foundations.  Change into
the directory you want to work with and get into a Nix shell:

```console
$ cd volume-3-verified-functional-algorithms/
$ nix develop
```

From the Nix shell, you should be able to build the source code:

```console
$ make
```

Then you should be able to open any `*.v` Coq file in `coqide`.  For example:

```console
$ coqide Sub.v
```

Or in VS Codium using the `vscoq` extension:

```console
$ codium Sub.v
```
