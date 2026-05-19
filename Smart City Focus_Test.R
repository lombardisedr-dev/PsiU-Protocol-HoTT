# PsiU-Protocol Engine: Smart City Focus
analyze_urban_resonance <- function(pm25_data) {
  # Definizione delle librerie di risonanza (Soglie HoTT)
  threshold_necessity <- 0.01
  threshold_possibility <- 0.10
  
  # Calcolo dello scostamento logico (Scotoma)
  # Usiamo il log-ratio per stabilizzare la varianza dei picchi urbani
  scotoma <- abs(diff(log(pm25_data)))
  
  # Classificazione secondo il protocollo PsiU
  results <- data.frame(
    valore = pm25_data[-1],
    scotoma = scotoma,
    status = ifelse(scotoma < threshold_necessity, "BOX (Necessity)",
             ifelse(scotoma < threshold_possibility, "DIAMOND (Possibility)", 
                    "NOISE (Accident)"))
  )
  
  # Verdetto di integrità del sistema
  convergence_rate <- mean(results$status != "NOISE (Accident)")
  cat("Systemic Status:", ifelse(convergence_rate > 0.5, "CONVERGENT", "NON_CONVERGENT"), "\n")
  
  return(results)
}

# Esempio con dati reali simulati (Pechino)
dati_aria <- c(120, 122, 121, 450, 430, 115) # 450 è un picco accidentale
test_city <- analyze_urban_resonance(dati_aria)
print(test_city)
