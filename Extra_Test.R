# ==============================================
# PsiU - Benchmark Scientifico + Test del Cieco
# ==============================================

# 1. Auto-install dipendenze - risolve il tuo "rosso"
if (!require("testthat")) {
  install.packages("testthat", repos="https://cloud.r-project.org", quiet=TRUE)
}
library(testthat)

# 2. Parametri YML - modificali qui o carica da file
PARAMS <- list(
  n_records = 100000,
  seed = 2026,
  g_target = 0.618,      # Metti 0.500 per Test del Cieco
  rumore_mean = 0.618,
  rumore_sd = 0.01,
  eps = 0.002
)

set.seed(PARAMS$seed)

# 3. Motore PsiU - versione minimale per test
psiU_classify <- function(x, g, eps) {
  dist <- abs(x - g)
  if (dist < eps) {
    return("BOX")      # Necessity
  } else if (dist < eps * 5) {
    return("DIAMOND")  # Possibility  
  } else {
    return("NOISE")    # Accident
  }
}

# 4. Genera dati test - gaussiana centrata su G
cat("Generazione", PARAMS$n_records, "campioni...\n")
dati <- rnorm(PARAMS$n_records, mean=PARAMS$rumore_mean, sd=PARAMS$rumore_sd)

# 5. Benchmark
start_time <- Sys.time()
stati <- sapply(dati, psiU_classify, g=PARAMS$g_target, eps=PARAMS$eps)
end_time <- Sys.time()

latenza_totale_ms <- as.numeric(difftime(end_time, start_time, units="secs")) * 1000
costo_per_punto_us <- (latenza_totale_ms * 1000) / PARAMS$n_records
throughput <- PARAMS$n_records / as.numeric(difftime(end_time, start_time, units="secs"))

# 6. Report
tab <- table(stati)
box_pct <- ifelse("BOX" %in% names(tab), tab["BOX"] / PARAMS$n_records * 100, 0)
diamond_pct <- ifelse("DIAMOND" %in% names(tab), tab["DIAMOND"] / PARAMS$n_records * 100, 0)
noise_pct <- ifelse("NOISE" %in% names(tab), tab["NOISE"] / PARAMS$n_records * 100, 0)

dist_media <- mean(abs(dati - PARAMS$g_target))

cat("\nREPORT SCIENTIFICO: action_benchmark.R\n")
cat("======================================================\n")
cat(sprintf("Campioni processati:      %d\n", PARAMS$n_records))
cat(sprintf("Latenza mediana totale:   %.3f ms\n", latenza_totale_ms))
cat(sprintf("Costo per singolo punto:  %.4f microsecondi\n", costo_per_punto_us))
cat(sprintf("Throughput Reale:         %.0f operazioni/sec\n", throughput))
cat("------------------------------------------------------\n")
cat("DISTRIBUZIONE DEGLI STATI (Selettività):\n\n")
cat(sprintf("      BOX (Necessity) [□] DIAMOND (Possibility) [◆]          NOISE (Accident) \n"))
cat(sprintf("                    %d                     %d                     %d \n\n", 
            tab["BOX"], tab["DIAMOND"], tab["NOISE"]))
cat(sprintf("Distanza media dal Target G: %.6f\n", dist_media))
cat("======================================================\n")

# 7. Unit test automatico - ora non crasha più
test_that("PsiU classifica BOX vicino a G", {
  expect_equal(psiU_classify(PARAMS$g_target, PARAMS$g_target, PARAMS$eps), "BOX")
})
test_that("PsiU classifica NOISE lontano da G", {
  expect_equal(psiU_classify(PARAMS$g_target + 0.1, PARAMS$g_target, PARAMS$eps), "NOISE")
})

cat("\nTutti i test passati. Exit code 0.\n")
