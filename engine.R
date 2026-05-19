# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE v1.2
# AUTORE  : Roberto Lombardi 
# LICENZA : [MIT]
# 
# DESCRIZIONE:
# Implementazione della Funzione di Risonanza Baricentrica per l'estrazione
# del "Nucleo Tautologico" (1/3 o Sezione Aurea) da dataset complessi.
# Il sistema applica un filtro esponenziale per isolare i punti di equilibrio
# strutturale, minimizzando il rumore attraverso la cristallizzazione gnomonica.
# ==============================================================================


target_gnomonic <- 1/3

# 1. Gestione Input
if(!file.exists("input_potential.csv")) {
  set.seed(333)
  write.csv(data.frame(u=1:1000, ratio=runif(1000, 0, 1)), "input_potential.csv", row.names=F)
}
S <- read.csv("input_potential.csv")

# 2. Calcolo Risonanza (J-Rule)
S$dist_ident <- abs(S$ratio - target_gnomonic)
S$resonance <- exp(-S$dist_ident / sd(S$ratio))

# 3. Test Modale (Necessità Box)
test_box <- t.test(S$ratio, mu = target_gnomonic)

# 4. Estrazione Nucleo (Onestà Scientifica)
threshold <- quantile(S$dist_ident, 0.10)
nucleo <- S[S$dist_ident <= threshold, ]

# --- 4. CREAZIONE MULTILIBRARY DI RISONANZA ---
# Definisco le Library in base allo scostamento numerico dal target (1/3)
S$scostamento <- abs(S$ratio - target_gnomonic)

S$library_status <- cut(S$scostamento, 
                       breaks = c(-Inf, 0.01, 0.10, Inf), 
                       labels = c("Library_1 (Necessità)", 
                                  "Library_0 (Possibilità)", 
                                  "Library_-1 (Rumore)"))

# Aggiungo il grado di intensità (0 a 1)
S$intensita_risonanza <- round(exp(-S$scostamento * 10), 4)

# --- 5. AGGIORNAMENTO OUTPUT ---
# Il nucleo ora contiene solo la Library 1
nucleo <- S[S$library_status == "Library_1 (Necessità)", ]


