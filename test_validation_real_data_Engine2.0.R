# PSI-U V3 TEST VALIDATION REAL DATA ENGINE 2.0
# Author: Roberto Lombardi | 13/06/2026 | CC BY-NC-ND 4.0

# Requisito: Engine 2.0 già caricato in R
# Dataset: datasets::co2 - Base R

data("co2")
real_signal <- as.numeric(co2)
set.seed(13062026)

real_report <- PsiU_Complete_MultiLibrary_V3(real_signal, block_size = 100)
print(real_report)

# Output deve matchare benc_validation_real_data_Engine2.0_CO2_*.csv
