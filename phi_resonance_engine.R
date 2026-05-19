# --- MOTORE DI CRISTALLIZZAZIONE AUREA ---
# Target: Sezione Aurea (Phi) - L'armonia della forma

if (!dir.exists("output_tautology")) dir.create("output_tautology")

# 1. Costanti Universali
phi <- (sqrt(5) - 1) / 2 # 0.6180339887...
epsilon <- 0.02          # Tolleranza ridotta per una "selezione" più severa

# 2. Caricamento Dati
if (file.exists("input_potential.csv")) {
  data <- read.csv("input_potential.csv")
} else {
  # Generiamo un set di dati più vasto per cercare l'armonia nascosta
  data <- data.frame(id = 1:1000, ratio = runif(1000, 0, 1))
}

# 3. Filtro di Risonanza Aurea
data$resonance <- exp(-abs(data$ratio - phi) / epsilon)

# 4. Estrazione del Nucleo (Soglia di Cristallo)
nucleo_aureo <- data[data$resonance > 0.6, ]

# 5. Scrittura Risultati
write.csv(nucleo_aureo, "output_tautology/golden_core.csv", row.names = FALSE)

cat("--- RISONANZA AUREA COMPLETATA ---\n")
cat("Punti di equilibrio trovati:", nrow(nucleo_aureo), "\n")
