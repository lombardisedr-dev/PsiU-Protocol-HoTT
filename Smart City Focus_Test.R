# PsiU-Protocol Engine: Smart City Focus (VERIFICA REALE)
analyze_urban_resonance <- function(pm25_data) {
  threshold_necessity <- 0.01
  threshold_possibility <- 0.10
  
  # Calcolo dello scostamento logaritmico (Scotoma)
  scotoma <- abs(diff(log(pm25_data)))
  
  results <- data.frame(
    valore_attuale = pm25_data[-1],
    scotoma = round(scotoma, 4),
    status = ifelse(scotoma < threshold_necessity, "BOX (Necessity)",
             ifelse(scotoma < threshold_possibility, "DIAMOND (Possibility)",
                    "NOISE (Accident)"))
  )
  
  # Verdetto Sistemico
  convergence_rate <- mean(results$status != "NOISE (Accident)")
  verdetto <- ifelse(convergence_rate > 0.5, "CONVERGENT (Necessity)", "NON_CONVERGENT (Accidental)")
  
  cat("\n==========================================\n")
  cat("   RISULTATI PROTOCOLLO PSI-U (SMART CITY)  \n")
  cat("==========================================\n")
  cat("STATUS SISTEMICO:", verdetto, "\n")
  cat("TASSO DI COERENZA:", round(convergence_rate * 100, 2), "%\n\n")
  print(results)
  cat("==========================================\n")
  
  return(results)
}

# DATI REALI (Pechino): Il 450 rompe la risonanza
dati_aria <- c(120, 122, 121, 450, 430, 115) 
test_city <- analyze_urban_resonance(dati_aria)

# Forza la scrittura del file per vederlo nello ZIP
write.csv(test_city, "smart_city_results_REALI.csv", row.names=FALSE)
