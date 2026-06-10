#' @file action_benchmark.R
#' @title Validazione Scientifica delle Performance di PsiUEngineRL
#' @description Test rigoroso su latenza, throughput e selettività modale.

if (!requireNamespace("microbenchmark", quietly = TRUE)) install.packages("microbenchmark")
library(microbenchmark)

# --- 1. PREPARAZIONE DEL CAMPIONE SCIENTIFICO ---
# Generiamo 100.000 osservazioni per avere una massa critica significativa.
# Simuliamo un segnale oscillante attorno al Gnomonic Ratio con rumore variabile.
set.seed(2026)
n_samples <- 100000
G <- 0.6180339887
raw_data <- G + (runif(n_samples, -0.015, 0.015) * rnorm(n_samples))

# --- 2. BENCHMARK DI LATENZA (L'Azione Scientifica) ---
cat("Esecuzione Benchmark su", n_samples, "punti... \n")

bench_results <- microbenchmark(
  core_engine = PsiU_Engine_RL(raw_data),
  times = 50, # 50 ripetizioni per stabilizzare la varianza
  unit = "ms"
)

# --- 3. ANALISI DEI RISULTATI (Statistica Descrittiva) ---
stats <- summary(bench_results)
total_time_ms <- stats$median
time_per_point_us <- (total_time_ms * 1000) / n_samples
points_per_second <- 1000000 / time_per_point_us

# --- 4. ANALISI DELLA SELETTIVITÀ (Verifica Scientifica della Logica) ---
analysis <- PsiU_Engine_RL(raw_data)
counts <- table(analysis$Stato_Modale)
dist_mean <- mean(analysis$Distanza_G)

# --- 5. REPORT FINALE ---
cat("\n======================================================\n")
cat("      REPORT SCIENTIFICO: action_benchmark.R         \n")
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
