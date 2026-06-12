set.seed(2026)
n <- 1000000  # 1M basta, 10M se vuoi torturarti

# 1. Genera rumore puro. Zero aureo dentro.
rumore <- rnorm(n, mean=0.618, sd=0.01)  # media su G per non barare

# 2. La TUA funzione PsiU_Engine_RL - incollala qui
# PsiU_Engine_RL <- function(x, g, eps=0.002) { ... }

# 3. Test A: G corretto
res_A <- PsiU_Engine_RL(rumore, g=0.618, eps=0.002)
box_A <- mean(res_A == "BOX") * 100

# 4. Test B: G sbagliato volutamente 
res_B <- PsiU_Engine_RL(rumore, g=0.500, eps=0.002) 
box_B <- mean(res_B == "BOX") * 100

# 5. Verdetto
cat("BOX% con G=0.618:", round(box_A, 4), "%\n")
cat("BOX% con G=0.500:", round(box_B, 4), "%\n")
cat("Delta:", round(abs(box_A - box_B), 4), "%\n")

if(abs(box_A - box_B) < 0.05) {
  cat("VERDETTO: FILTRO BANALE. Non usa G, usa solo eps\n")
} else {
  cat("VERDETTO: USA G. Non è solo abs(x-const)<eps\n")
}
