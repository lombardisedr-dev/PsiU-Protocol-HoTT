library(PsiUEngineRL)  # Nome CRAN corretto
library(tictoc)
set.seed(2026)

N <- 10000000
G <- 0.6180339887

cat("PsiUEngineRL v", as.character(packageVersion("PsiUEngineRL")), "- 10M Test\n")
cat("START:", format(Sys.time(), "%Y-%m-%d %H:%M:%S %Z"), "\n\n")

# TEST 1: BOX PURO
tic("BOX 10M")
ris_box <- PsiU_Engine_RL(rep(G, N))
tempo_box <- toc(quiet = TRUE)
box_rate <- mean(ris_box$Stato_Modale == "BOX (Necessity) [\u25a1]")

# TEST 2: NOISE PURO  
tic("NOISE 10M")
ris_noise <- PsiU_Engine_RL(rnorm(N))
tempo_noise <- toc(quiet = TRUE)
noise_rate <- mean(ris_noise$Stato_Modale == "BOX (Necessity) [\u25a1]")
fp_totali <- sum(ris_noise$Stato_Modale == "BOX (Necessity) [\u25a1]")
dist_noise <- table(ris_noise$Stato_Modale)

cat("=== VERDETTO 10M PsiUEngineRL ===\n")
cat("Package:", "PsiUEngineRL", as.character(packageVersion("PsiUEngineRL")), "\n")
cat("N:", N, "Seed:", 2026, "\n\n")
cat("BOX su segnale G puro :", sprintf("%.6f%%", box_rate * 100), "\n")
cat("BOX su rumore N(0,1)  :", sprintf("%.6f%%", noise_rate * 100), "FP\n")
cat("Falsi Positivi totali :", fp_totali, "\n")
cat("Tempo BOX:", round(tempo_box$toc - tempo_box$tic, 2), "s\n")
cat("Tempo NOISE:", round(tempo_noise$toc - tempo_noise$tic, 2), "s\n\n")
cat("Distribuzione NOISE:\n")
print(dist_noise)
cat("\nEND:", format(Sys.time(), "%Y-%m-%d %H:%M:%S %Z"), "\n")

write.csv(data.frame(
  package = "PsiUEngineRL",
  version = as.character(packageVersion("PsiUEngineRL")),
  N = N,
  seed = 2026,
  box_rate_puro = box_rate,
  fp_rate_noise = noise_rate,
  fp_totali = fp_totali,
  box_noise = as.numeric(dist_noise["BOX (Necessity) [\u25a1]"]),
  diamond_noise = as.numeric(dist_noise["DIAMOND (Possibility) [\u25c6]"]),
  noise_noise = as.numeric(dist_noise["NOISE (Accident)"]),
  tempo_box_s = as.numeric(tempo_box$toc - tempo_box$tic),
  tempo_noise_s = as.numeric(tempo_noise$toc - tempo_noise$tic),
  timestamp_utc = format(Sys.time(), "%Y-%m-%d %H:%M:%S", tz = "UTC")
), "risultati_10M_PsiUEngineRL.csv", row.names = FALSE)
