# =================================================================
# PROJECT:  PsiU-Protocol Artifact Generator (100% Native R)
# MODULE:   Homotopy Type Theory, Modal Logic Engine & Graphics
# LICENSE:  MIT
# =================================================================

# --- 1. CONFIGURAZIONE DEL CODICE LOGICO DA SALVARE ---
r_engine_code <- '
G <- 0.6180339887  
BOX_THRESHOLD     <- 0.002  
DIAMOND_THRESHOLD <- 0.010  

create_hott_type <- function(value, type_label) {
  structure(list(val = value, type = type_label), class = "HoTT_Type")
}

create_path <- function(type_a, type_b, tolerance) {
  if (type_a$type != type_b$type) return(NULL) 
  distance <- abs(type_a$val - type_b$val)
  if (distance <= tolerance) {
    return(list(from = type_a, to = type_b, distance = distance, proof = "Reflexivity_Path"))
  } else {
    return(NULL) 
  }
}

j_rule <- function(path, property_A, property_B) {
  if (is.null(path)) return("NOISE (Accident)")
  if (path$distance <= BOX_THRESHOLD) return(property_A) 
  if (path$distance <= DIAMOND_THRESHOLD) return(property_B) 
}

psiu_hott_engine <- function(raw_input_vector) {
  G_target <- create_hott_type(G, "Gnomonic_Ratio")
  prop_A   <- "BOX (Necessity) [□fgno]"
  prop_B   <- "DIAMOND (Possibility) [♢fgno]"
  states  <- character(length(raw_input_vector))
  offsets <- numeric(length(raw_input_vector))
  for (i in 1:length(raw_input_vector)) {
    current_u <- create_hott_type(raw_input_vector[i], "Gnomonic_Ratio")
    path_to_G <- create_path(current_u, G_target, tolerance = DIAMOND_THRESHOLD)
    states[i] <- j_rule(path_to_G, prop_A, prop_B)
    offsets[i] <- abs(raw_input_vector[i] - G)
  }
  return(data.frame(Valore_Grezzo = raw_input_vector, Distanza_G = round(offsets, 5), Stato_Modale = states, stringsAsFactors = FALSE))
}

generate_resonance_map <- function(engine_results) {
  color_map <- c("BOX (Necessity) [□fgno]" = "#2ecc71", "DIAMOND (Possibility) [♢fgno]" = "#f1c40f", "NOISE (Accident)" = "#95a5a6")
  p_colors <- color_map[engine_results$Stato_Modale]
  
  png("psi_u_resonance_map.png", width = 1000, height = 600, res = 120)
  plot(engine_results$Valore_Grezzo, col = p_colors, pch = 19, cex = 0.8,
       main = "PsiU-Protocol: Mappa di Risonanza Logico-Modale", xlab = "Indice del Campione", ylab = "Valore Rilevato", ylim = c(G - 0.02, G + 0.02))
  rect(0, G - DIAMOND_THRESHOLD, nrow(engine_results), G + DIAMOND_THRESHOLD, col = rgb(241, 196, 15, alpha = 25, maxColorValue = 255), border = NA)
  rect(0, G - BOX_THRESHOLD, nrow(engine_results), G + BOX_THRESHOLD, col = rgb(46, 204, 113, alpha = 40, maxColorValue = 255), border = NA)
  abline(h = G, col = "#e74c3c", lwd = 2, lty = 2)
  legend("topright", legend = c("BOX (□)", "DIAMOND (♢)", "NOISE", "G (0.618)"), col = c("#2ecc71", "#f1c40f", "#95a5a6", "#e74c3c"), pch = c(19,19,19,NA), lty = c(NA,NA,NA,2), lwd = c(NA,NA,NA,2), bg = "white")
  dev.off()
}

generate_advanced_report <- function(engine_results) {
  is_noise <- engine_results$Stato_Modale == "NOISE (Accident)"
  scostamenti_noise <- engine_results$Distanza_G[is_noise]
  scostamenti_normali <- engine_results$Distanza_G[!is_noise]
  
  media_normali <- mean(scostamenti_normali)
  sd_normali <- sd(scostamenti_normali)
  if (sd_normali == 0 || is.na(sd_normali)) sd_normali <- 1e-6
  scostamento_sigma <- mean((scostamenti_noise - media_normali) / sd_normali)
  
  if (length(scostamenti_noise) > 1) {
    dens_noise <- density(scostamenti_noise)
    modalita_valore <- dens_noise$x[which.max(dens_noise$y)]
  } else {
    modalita_valore <- mean(scostamenti_noise)
  }
  
  if (sum(is_noise) > 1) {
    dist_interne <- as.matrix(dist(engine_results$Valore_Grezzo[is_noise]))
    risonanza_indice <- 1 / mean(dist_interne[dist_interne > 0])
  } else {
    risonanza_indice <- 0
  }
  
  report_output <- c(
    "=================================================",
    "    REPORT DI RISONANZA E SCOSTAMENTO (PsiU-ADV) ",
    "=================================================",
    sprintf("Data/Ora Analisi: %s", Sys.time()),
    sprintf("Campioni Totali Analizzati: %d", nrow(engine_results)),
    sprintf("Campioni Classificati come NOISE: %d", sum(is_noise)),
    "-------------------------------------------------",
    "METRICHE RIGOROSE DI SCOSTAMENTO DAL RANGE:",
    sprintf("  - Scostamento Medio dal Range: %.2f Sigma (Deviazioni Standard)", scostamento_sigma),
    sprintf("  - Modalita dello Scostamento: %.6f (Punto critico di frequenza)", modalita_valore),
    sprintf("  - Indice di Risonanza Strutturale: %.6f (Pattern Geometrico)", risonanza_indice),
    "================================================="
  )
  
  writeLines(report_output)
  writeLines(report_output, "report_scostamenti.txt")
}

set.seed(42)
campioni_test <- c(runif(300, min = G - 0.001, max = G + 0.001), runif(300, min = G - 0.009, max = G + 0.009), runif(400, min = G - 0.030, max = G + 0.030))
risultati <- psiu_hott_engine(campioni_test)
generate_resonance_map(risultati)
generate_advanced_report(risultati)

cat("\n--- STRESS TEST COMPLETATO ---\n")
print(table(risultati$Stato_Modale))
'

# --- 2. SCRITTURA FISICA DEL FILE .R SUL DISCO (Spazi Corretti) ---
writeLines(r_engine_code, "PsiU_Protocol_Engine.R")

# --- 3. COMPILAZIONE E GENERAZIONE AUTOMATICA DEGLI ARTIFACTS (Spazi Corretti) ---
source("PsiU_Protocol_Engine.R")

# --- 4. VERIFICA DELLA CREAZIONE DEI FILE ---
cat("\n=======================================================\n")
cat("          GENERAZIONE ARTIFACTS COMPLETATA!             \n")
cat("=======================================================\n")
cat("I seguenti file sono stati creati nella tua cartella:\n")
cat(" -> ", getwd(), "/PsiU_Protocol_Engine.R (Codice R)\n", sep="")
cat(" -> ", getwd(), "/psi_u_resonance_map.png (Mappa Grafica)\n", sep="")
cat(" -> ", getwd(), "/report_scostamenti.txt (Report di Analisi)\n", sep="")
cat("=======================================================\n")
