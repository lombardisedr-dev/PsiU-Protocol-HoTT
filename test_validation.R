library(testthat)

test_that("1. Test SCADA L-Town", {
  finto_scada <- data.frame(pressure = c(1.2, 1.5, 1.1))
  risultato <- action_ltown_scada(finto_scada)
  expect_false(is.null(risultato))
})

test_that("2. Test MIT-BIH Clinical", {
  finto_ecg <- c(0.5, 0.6, 0.5, 0.4)
  risultato <- action_mitbih_clinical(finto_ecg)
  expect_false(is.null(risultato))
})

test_that("3. Test Quantum Coherence", {
  finto_tensor <- c(1, 0, 0, 1)
  risultato <- action_quantum_coherence(finto_tensor)
  expect_false(is.null(risultato))
})

test_that("4. Test Smart Cities IoT", {
  finto_iot <- c(22.5, 23.0, 21.9)
  risultato <- action_smart_cities(finto_iot)
  expect_false(is.null(risultato))
})
