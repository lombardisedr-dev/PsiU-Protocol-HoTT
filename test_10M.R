# Test 10M - Motore Modale Gnomonico
# seed=2026 per riproducibilità totale

library(MotoreModale) # il tuo package
set.seed(2026)

N <- 10000000
G_TARGET <- 0.6180339887

cat("START 10M Test -", Sys.time(), "\n")

# 1. BOX puro: 10M punti deterministici
tictoc::tic("BOX 10M")
box_data <- sequenza_gnomonica(N, phi = G_TARGET)
ris_box <- motore_modale(box_data, target = G_TARGET)
tictoc::toc()
box_rate <- sum(ris_box == "BOX") / N

# 2. NOISE puro: 10M punti gaussiani 
tictoc::tic("NOISE 10M")
noise_data <- rnorm(N, mean = 0, sd = 1)
ris_noise <- motore_modale(noise_data, target = G_TARGET)
tictoc::toc()
noise_rate <- sum(ris_noise == "BOX") / N

# 3. Verdetto
cat("\n=== VERDETTO 10M ===\n")
cat("BOX rilevati su segnale puro:", box_rate * 100, "%\n")
cat("BOX rilevati su rumore puro:", noise_rate * 100, "%\n")
cat("Falsi Positivi:", noise_rate * N, "\n")
cat("Falsi Negativi:", (1 - box_rate) * N, "\n")
cat("END 10M Test -", Sys.time(), "\n")

# Salva per r/inferencesystems
write.csv(data.frame(
  N = N,
  box_rate = box_rate,
  noise_rate = noise_rate,
  seed = 2026,
  timestamp = Sys.time()
), "risultati_10M.csv", row.names = FALSE)
