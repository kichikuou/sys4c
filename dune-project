(lang dune 2.8)
(using menhir 2.1)

(generate_opam_files true)

(package
  (name sys4c)
  (synopsis "Compiler for the System 4 programming language.")
  (description "\| A compiler for AliceSoft's System 4
               "\| programming language.
               )
  (depends
   ocaml
   base
   cmdliner
   stdio
   camlzip
   vector
   dune
   menhir
   yojson
   (ppx_expect :with-test)
   (ocamlformat (= 0.27.0))))
