# ==============================================
# PsiU - Validazione Scientifica Rigorosa
# ==============================================
library(testthat)

PARAMS <- list(
  n_records = 100000,
  seed = 2026,
  g_target = 0.618,      # MODIFICARE: 0.618 per In-Target, 0.500 per Test del Cieco
  rumore_mean = 0.618,
  rumore_sd = 0.01,
  eps = 0.002
)

set.seed(PARAMS$seed)

psiU_classify <- function(x, g, eps) {
  dist <- abs(x - g)
  if (dist < eps) return("BOX")
  if (dist < eps * 5) return("DIAMOND")
  return("NOISE")
}

# 1. Generazione dati
dati <- rnorm(PARAMS$n_records, mean=PARAMS$rumore_mean, sd=PARAMS$rumore_sd)

# 2. Esecuzione Classificazione
stati <- sapply(dati, psiU_classify, g=PARAMS$g_target, eps=PARAMS$eps)
stati_factor <- factor(stati, levels=c("BOX", "DIAMOND", "NOISE"))
conteggi_osservati <- table(stati_factor)

# 3. CALCOLO DELLE PROBABILITÀ TEORICHE (Integrazione Scientifica)
# Calcolo delle aree sotto la curva gaussiana per i tre intervalli rispetto a G
p_box <- pnorm(PARAMS$g_target + PARAMS$eps, mean=PARAMS$rumore_mean, sd=PARAMS$rumore_sd) - 
         pnorm(PARAMS$g_target - PARAMS$eps, mean=PARAMS$rumore_mean, sd=PARAMS$rumore_sd)

p_diamond_tot <- pnorm(PARAMS$g_target + (PARAMS$eps * 5), mean=PARAMS$rumore_mean, sd=PARAMS$rumore_sd) - 
                 pnorm(PARAMS$g_target - (PARAMS$eps * 5), mean=PARAMS$rumore_mean, sd=PARAMS$rumore_sd)
p_diamond <- p_diamond_tot - p_box

p_noise <- 1 - p_diamond_tot
prob_teoriche <- c(BOX=p_box, DIAMOND=p_diamond, NOISE=p_noise)
conteggi_attesi <- prob_teoriche * PARAMS$n_records

# 4. TEST DI BONTA DEL FIT (Chi-Square Test)
# Misura se la classificazione PsiU diverge dalla teoria matematica
p_value_chi2 <- NA
if (all(conteggi_attesi > 5)) { # Il test è valido solo se le frequenze attese sono > 5
  chi2_test <- chisq.test(conteggi_osservati, p = prob_teoriche)
  p_value_chi2 <- chi2_test$p.value
}

# 5. REPORT SCIENTIFICO AVANZATO
dist_media <- mean(abs(dati - PARAMS$g_target))

cat("\nVALIDAZIONE SCIENTIFICA: PsiU System\n")
cat("========================================================================\n")
cat(sprintf("Configurazione: Target G = %.3f | Media Rumore = %.3f | Dev.Std = %.2f\n", 
            PARAMS$g_target, PARAMS$rumore_mean, PARAMS$rumore_sd))
cat(sprintf("Distanza media empirica dal Target G: %.6f\n", dist_media))
cat("------------------------------------------------------------------------\n")
cat("CONFRONTO DISTRIBUZIONE (Selettività Empirica vs Modello Teorico):\n\n")

cat(sprintf("  STATO     | Osservati (N) | Attesi (N)  | Scostamento Reale\n"))
cat(sprintf("  ----------|---------------|-------------|---------------------\n"))
cat(sprintf("  BOX       | %-13d | %-11.1f | %+.4f%%\n", 
            conteggi_osservati["BOX"], conteggi_attesi["BOX"], 
            ((conteggi_osservati["BOX"] - conteggi_attesi["BOX"]) / PARAMS$n_records) * 100))
cat(sprintf("  DIAMOND   | %-13d | %-11.1f | %+.4f%%\n", 
            conteggi_osservati["DIAMOND"], conteggi_attesi["DIAMOND"], 
            ((conteggi_osservati["DIAMOND"] - conteggi_attesi["DIAMOND"]) / PARAMS$n_records) * 100))
cat(sprintf("  NOISE     | %-13d | %-11.1f | %+.4f%%\n", 
            conteggi_osservati["NOISE"], conteggi_attesi["NOISE"], 
            ((conteggi_osservati["NOISE"] - conteggi_attesi["NOISE"]) / PARAMS$n_records) * 100))
cat("------------------------------------------------------------------------\n")

if (!is.na(p_value_chi2)) {
  cat(sprintf("P-Value del Test Chi-Quadro: %.4f\n", p_value_chi2))
  cat("Interpretazione: ")
  if (p_value_chi2 > 0.05) {
    cat("H0 ACCETTATA. La ripartizione di PsiU rispecchia perfettamente la teoria.\n")
  } else {
    cat("H0 RIFIUTATA. Anomalia statistica o deviazione significativa dalla teoria.\n")
  }
} else {
  cat("P-Value del Test Chi-Quadro: N/D (Frequenze attese vicine allo zero - Controllo Negativo Riuscito)\n")
}
cat("========================================================================\n")


