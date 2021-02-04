(prover
  (name pzm)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-brwrt)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -brwrt $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-sko)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -modsko $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-sko-brwrt)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -modsko -brwrt $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-sko-mini)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -modsko -modminiscope $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-sko-mini-brwrt)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -modsko -modminiscope -brwrt $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-arith)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -x arith $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-arith-brwrt)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -x arith -brwrt $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-arith-sko)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -x arith -modsko $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-arith-sko-brwrt)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -x arith -modsko -brwrt $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-arith-sko-mini)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -x arith -modsko -modminiscope $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-arith-sko-mini-brwrt)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -x arith -modsko -modminiscope -brwrt $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name pzm-arith-sko-mini-brwrt)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -x arith -modsko -modminiscope -brwrt $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))

(prover
  (name vampire)
  (binary "${cur_dir}/vampire.sh")
  (cmd "${cur_dir}/vampire.sh $file")
  (sat "Refutation$")
  (unknown "Refutation not found")
  (timeout "Time limit"))
(prover
  (name alt-ergo)
  (binary "${cur_dir}/alt-ergo.sh")
  (cmd "${cur_dir}/alt-ergo.sh $file")
  (sat "unsat")
  (unsat "sat"))


(dir
  (path "${cur_dir}/basic")
  (pattern ".*\\.(p)")
  (expect (const sat))
  )

(task
  (name comp-zp)
  (synopsis "Compare all version of polarised zenon")
  (action
    (run_provers
      (provers 
        pzm pzm-brwrt pzm-sko pzm-sko-brwrt pzm-sko-mini
        pzm-sko-mini-brwrt pzm-arith pzm-arith-brwrt 
        pzm-arith-sko pzm-arith-sko-brwrt pzm-arith-sko-mini
        pzm-arith-sko-mini-brwrt)
      (timeout 60)
      (dirs "${cur_dir}/basic"))))

(task
  (name test-other)
  (synopsis "Compare all version of polarised zenon")
  (action
    (run_provers
      (provers pzm-arith-sko-mini-brwrt vampire alt-ergo)
      (timeout 60)
      (dirs "${cur_dir}/basic"))))


(set-options 
    (j 4)
    (progress true))
