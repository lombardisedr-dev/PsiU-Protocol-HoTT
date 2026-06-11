# -------------------------------------------------------------------------
# PROTOCOLLO DI AUDIT SCIENTIFICO: VALIDAZIONE DELLA GNOMONIC RATIO
# -------------------------------------------------------------------------
library(PsiUEngineRL)

# Impostazione del seed per la riproducibilità universale
set.seed(2026)
n_punti <- 500

# 1. GENERAZIONE DEI FLUSSI COMPORTAMENTALI
flusso_box   <- sin(seq(0, 4 * pi, length.out = n_punti))                      # Segnale geometrico stabile
flusso_dia   <- cumsum(rnorm(n_punti, mean = 0.01, sd = 0.05))                 # Cammino casuale coerente
flusso_noise <- rnorm(n_punti, mean = 0, sd = 2.5)                             # Entropia pura senza geodetica

# 2. PROCESSAMENTO CON IL MOTORE HoTT
print("[INFO] Esecuzione del motore su flussi differenziati...")
res_box   <- PsiU_Engine_RL(flusso_box)
res_dia   <- PsiU_Engine_RL(flusso_dia)
res_noise <- PsiU_Engine_RL(flusso_noise)

# 3. ESTRAZIONE DELLE METRICHE DI ENTROPIA STRUTTURALE
# Valutiamo la deviazione dei cammini di identità dalla Gnomonic Ratio invariante
metriche <- data.frame(
  Tipo = c(rep("Necessita", n_punti), rep("Possibilita", n_punti), rep("Rumore", n_punti)),
  Entropia = c(res_box$structural_entropy, res_dia$structural_entropy, res_noise$structural_entropy)
)

# 4. TEST DI INECCEPIBILITÀ STATISTICA (ANOVA + Post-Hoc Tukey)
# Dimostriamo se la Gnomonic Ratio distingue in modo statisticamente significativo i tre domini
modello_anova <- aov(Entropia ~ Tipo, data = metriche)
sintesi_anova <- summary(modello_anova)
test_tukey    <- TukeyHSD(modello_anova)

# 5. OUTPUT DEI RISULTATI DELLA VALIDAZIONE
print("=== RISULTATI DELL'ANOVA (VERIFICA DI SIGNIFICATIVITÀ) ===")
print(sintesi_anova)

print("=== CONFRONTI COPPIE TUKEY (DISTINGUIBILITÀ DELLA RATIO) ===")
print(test_tukey)
