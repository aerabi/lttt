<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Linear Temporal Type Theory

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/aerabi/lttt/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/aerabi/lttt/actions?query=workflow:"Docker%20CI"




An implementation of linear temporal types


## Meta

- Author(s):
  - Mohammad-Ali A'RÂBI
- License: [MIT license](LICENSE)
- Compatible Coq versions: Coq 8.7 to 8.11
- Additional dependencies:
  - Quickchick
- Coq namespace: `LTTT`
- Related publication(s):
  - [The Essence of Event-Driven Programming](https://128.232.0.20/~nk480/essence-of-events.pdf) 
  - [Linear Temporal Type Theory for Event-based Reactive Programming](https://www.semanticscholar.org/paper/Linear-Temporal-Type-Theory-for-Event-based-Paykin-Krishnaswami/4b8eccab1340c9d1035728ba5b198eab41ab66f3) 

## Building and installation instructions

The easiest way to install the latest released version of Linear Temporal Type Theory
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-lttt
```

To instead build and install manually, do:

``` shell
git clone https://github.com/aerabi/lttt.git
cd lttt
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



