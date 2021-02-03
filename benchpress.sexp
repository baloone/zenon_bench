(prover
  (name pzm)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -max-time ${timeout} $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))
(prover
  (name pzm-arith)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -x arith -max-time ${timeout} $file 2>&1)
  (sat "PROOF-FOUND"))
(prover
  (name pzm-sko)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -modsko -max-time ${timeout} $file")
  (timeout "time limit")
  (sat "PROOF-FOUND"))
(prover
  (name pzm-arith-sko)
  (binary "${cur_dir}/../zenon_modpol/znmh")
  (cmd "${cur_dir}/../zenon_modpol/znmh -modsko -x arith -max-time ${timeout} $file 2>&1)
  (sat "PROOF-FOUND"))


(dir
  (path "${cur_dir}/basic")
  (pattern ".*\\.(p)")
  (expect (const sat))
  )

(task
  (name basic)
  (synopsis "run mc2 on directories provided on the command line")
  (action
    (run_provers
      (provers pzm pzm-arith)
      (timeout 60)
      (dirs "${cur_dir}/basic"))))

(set-options 
    (j 4)
    (progress true))
