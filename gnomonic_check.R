#' @file gnomonic_check.R
#' @title Validazione Scientifica e Stress Test di PsiUEngineRL
#' @description Test di produzione su latenza, throughput e selettività topologica.

# --- 1. GESTIONE DIPENDENZE (Anti-Errore GitHub) ---
libs <- c("microbenchmark", "testthat", "PsiUEngineRL")
for (lib in libs) {
  if (!requireNamespace(lib, quietly = TRUE)) {
    install.packages(lib, repos = "https://r-project.org")
  }
  library(lib, character.only = TRUE)
}

# --- 2. PREPARAZIONE DEL CAMPIONE SCIENTIFICO ---
set.seed(2026)
n_samples <- 100000
G <- 0.6180339887
# Simuliamo un segnale attorno al Gnomonic Ratio con rumore variabile
raw_data <- G + (runif(n_samples, -0.015, 0.015) * rnorm(n_samples))

# --- 3. BENCHMARK DI PRESTAZIONE ---
cat("Esecuzione Benchmark su", n_samples, "punti... \n")

bench_results <- microbenchmark(
  core_engine = PsiU_Engine_RL(raw_data),
  times = 50, 
  unit = "ms"
)

# --- 4. CALCOLO METRICHE ---
stats <- summary(bench_results)
total_time_ms <- stats$median
time_per_point_us <- (total_time_ms * 1000) / n_samples
points_per_second <- 1000000 / time_per_point_us

# --- 5. ANALISI DELLA SELETTIVITÀ ---
analysis <- PsiU_Engine_RL(raw_data)
counts <- table(analysis$Stato_Modale)
dist_mean <- mean(analysis$Distanza_G)

# --- 6. REPORT SCIENTIFICO FINALE ---
cat("\n======================================================\n")
cat("      REPORT SCIENTIFICO: gnomonic_check.R           \n")
cat("======================================================\n")
cat(sprintf("Campioni processati:      %d\n", n_samples))
cat(sprintf("Latenza mediana totale:   %.3f ms\n", total_time_ms))
cat(sprintf("Costo per singolo punto:  %.4f microsecondi\n", time_per_point_us))
cat(sprintf("Throughput Reale:         %.0f operazioni/sec\n", points_per_second))
cat("------------------------------------------------------\n")
cat("DISTRIBUZIONE DEGLI STATI (Selettività):\n")
print(counts)
cat(sprintf("\nDistanza media dal Target G: %.6f\n", dist_mean))
cat("======================================================\n")

# --- 7. UNIT TEST DI VALIDAZIONE (testthat) ---
test_that("Performance e Logica sono conformi", {
  # Verifica che il throughput sia sopra una soglia minima accettabile (es. 50k ops/sec)
  expect_gt(points_per_second, 50000)
  
  # Verifica che la distanza dal Target G sia minima
  expect_lt(dist_mean, 0.01)
  
  # Verifica che il motore abbia identificato stati diversi (non tutto rumore)
  expect_gt(length(counts), 1)
})

cat("\n[SUCCESS] Il protocollo ha superato tutti i test di validazione.\n")
