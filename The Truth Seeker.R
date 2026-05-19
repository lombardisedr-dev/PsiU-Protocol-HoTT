# --- STEP 1: GENERAZIONE DATI ONETI E SCIENTIFICI ---
# Creiamo un dataset "ostile" con tre tipi di segnali:
set.seed(42) # Per rendere il test riproducibile

# 1. IL SEGNALE PURO (Verità): 100 punti vicinissimi a 1/3 (Target dell'autore)
verita <- rnorm(100, mean = 1/3, sd = 0.005)

# 2. LA CIVETTA (Falso Positivo): 100 punti vicini a 0.35 (fuori dalla "Necessità")
civetta <- rnorm(100, mean = 0.35, sd = 0.005)

# 3. IL RUMORE (Caos): 800 punti totalmente casuali tra 0 e 1
rumore <- runif(800, 0, 1)

# Uniamo tutto in un unico file come richiesto dal PsiU-Protocol
test_data <- data.frame(ratio = c(verita, civetta, rumore))
write.csv(test_data, "input_potential.csv", row.names = FALSE)

cat("--- FASE 1: Dataset 'input_potential.csv' generato con successo. ---\n")

# --- STEP 2: ESECUZIONE DEL MOTORE ORIGINALE ---
# Lanciamo il motore di Lombardi senza toccare una virgola del suo codice
source("engine.R")

# --- STEP 3: ANALISI SCIENTIFICA DEI RISULTATI ---
# Leggiamo cosa ha deciso il protocollo
risultati <- read.csv("results_full_analysis.csv")

# Calcoliamo l'efficienza ingegneristica
tot_necessity <- sum(risultati$library_status == " Library_1 (Necessity)")
tot_noise <- sum(risultati$library_status == " Library_-1 (Noise)")

# VERDETTO SCIENTIFICO
cat("\n--- RAPPORTO DI VALIDAZIONE FINALE ---\n")
cat("Punti di 'Verità' rilevati correttamente:", sum(risultati$library_status[1:100] == " Library_1 (Necessity)"), "/100\n")
cat("Punti 'Civetta' scartati correttamente:", sum(risultati$library_status[101:200] != " Library_1 (Necessity)"), "/100\n")
cat("Percentuale di Rumore filtrato:", round((sum(risultati$library_status[201:1000] == " Library_-1 (Noise)") / 800) * 100, 2), "%\n")

if (tot_necessity > 90 && tot_necessity < 120) {
  cat("\nRISULTATO: IL PROTOCOLLO È VALIDO E ALTAMENTE SELETTIVO.\n")
} else {
  cat("\nRISULTATO: IL PROTOCOLLO HA UN ERRORE DI TARATURA (TROPPI FALSI POSITIVI O NEGATIVI).\n")
}
