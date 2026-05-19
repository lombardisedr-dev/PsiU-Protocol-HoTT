# --- MOTORE DI CRISTALLIZZAZIONE GNOMONICA ---
# Questo script analizza i dati in input e applica il filtro 1/3

if (!dir.exists("output_tautology")) dir.create("output_tautology")

# 1. Caricamento Dati (Simula l'intersezione A inter B)
# Immaginiamo un file 'input_potential.csv' con una colonna 'ratio'
if (file.exists("input_potential.csv")) {
  data <- read.csv("input_potential.csv")
} else {
  # Se il file non esiste, generiamo rumore per il test
  data <- data.frame(id = 1:100, ratio = runif(100, 0, 1))
}

# 2. Funzione di Risonanza Baricentrica (Filtro 1/3)
epsilon <- 0.05 # Soglia di tolleranza della transizione di fase
data$resonance <- exp(-abs(data$ratio - (1/3)) / epsilon)

# 3. Estrazione Tautologica
# Solo ciò che ha una risonanza > 0.5 (Cristallo) sopravvive
nucleo_tautologico <- data[data$resonance > 0.5, ]

# 4. Scrittura dei Risultati (Cristallizzazione)
write.csv(nucleo_tautologico, "output_tautology/resonant_core.csv", row.names = FALSE)

# Log per la GitHub Action
cat("Analisi Completata.\n")
cat("Rami processati:", nrow(data), "\n")
cat("Nuclei cristallizzati:", nrow(nucleo_tautologico), "\n")
if(nrow(nucleo_tautologico) == 0) stop("Fallacia Totale: Nessun nucleo risonante trovato.")
