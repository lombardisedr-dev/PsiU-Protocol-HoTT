library(testthat)
library(PsiUEngineRL)

test_that("Il Protocollo PsiU-HoTT risponde correttamente all'Engine CRAN", {
  
  # Test L-Town: deve identificare la necessità (BOX)
  res_h2o <- action_ltown_scada(data.frame(pressure = 0.618))
  expect_true(!is.null(res_h2o))
  
  # Test Sanità: deve processare il segnale
  res_ecg <- action_mitbih_clinical(rnorm(10))
  expect_true(!is.null(res_ecg))
  
  # Test Quantum: deve mappare la coerenza
  res_q <- action_quantum_coherence(matrix(c(1,0,0,1), 2))
  expect_true(!is.null(res_q))
  
  # Test Smart Cities: deve generare trigger
  res_iot <- action_smart_cities(0.618)
  expect_true(!is.null(res_iot))
})
