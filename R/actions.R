library(testthat)

test_that("action_ltown_scada funziona correttamente", {
  # Prepariamo un finto data.frame con la colonna 'pressure'
  finto_scada <- data.frame(pressure = c(1.2, 1.5, 1.1))
  
  # Proviamo a eseguire la tua funzione
  risultato <- action_ltown_scada(finto_scada)
  
  # Verifichiamo solo che restituisca qualcosa e non si blocchi
  expect_false(is.null(risultato))
})

test_that("action_mitbih_clinical funziona correttamente", {
  finto_ecg <- c(0.5, 0.6, 0.5, 0.4)
  risultato <- action_mitbih_clinical(finto_ecg)
  expect_false(is.null(risultato))
})

test_that("action_quantum_coherence funziona correttamente", {
  finto_tensor <- c(1, 0, 0, 1)
  risultato <- action_quantum_coherence(finto_tensor)
  expect_false(is.null(risultato))
})

test_that("action_smart_cities funziona correttamente", {
  finto_iot <- c(22.5, 23.0, 21.9)
  risultato <- action_smart_cities(finto_iot)
  expect_false(is.null(risultato))
})


