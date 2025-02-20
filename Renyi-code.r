####################################################################### 
## Here we provide the R codes used in the paper                     ##
## 'Generalized Rényi statistics' by Péter Kevei and László Viharos. ##
#######################################################################


###########################################################
## Section 2.1 Quantile estimator
###########################################################

# Here we simulate the quantile estimator discussed in Section 2.1.

n <- 1000 # number of iid observations
N <- 1000 # number of iterations
gamma <- 0.5 # mean

# We simulate the iid $Z$ sequence from uniform, exponential, and Bernoulli distribution, 
# each with mean $0.5$. The square root of the corresponding variances:

sigmaunif <- 2*gamma/sqrt(12) 
sigmaexp <- gamma 
sigmabin <- 0.5 

# The $h(s)$ function explodes both at 0 and at 1. We use the grid s:
s <- seq(0.2, 0.99, 0.001)

# Auxiliary lists and matrices:
aux <- (n:1)
gammatilde <- rep(0, length(s)*N)
dim(gammatilde) <- c(length(s), N)
gammatildeexp <- rep(0, length(s)*N)
dim(gammatildeexp) <- c(length(s), N)
gammatildebin <- rep(0, length(s)*N)
dim(gammatildebin) <- c(length(s), N)

set.seed(100)
for (i in 1:N){
  sampleunif <- 2*gamma*runif(n) # uniform sample
  sampleexp <- rexp(n, rate = 1/gamma)  # exponential sample
  samplebin <- rbinom(n, 1, 0.5) # Bernoulli sample
  aux2 <- sampleunif/aux
  aux2exp <- sampleexp/aux
  aux2bin <- samplebin/aux
  Xunif <- cumsum(aux2) # the sequence X_{k,n}
  Xexp <- cumsum(aux2exp)
  Xbin <- cumsum(aux2bin)
  gammatilde[,i] <- Xunif[floor(n*s)]/(-log(1-s)) # estimate of gamma
  gammatildeexp[,i] <- Xexp[floor(n*s)]/(-log(1-s))
  gammatildebin[,i] <- Xbin[floor(n*s)]/(-log(1-s))
}

# The empirical variances:
stdgammaunif <- sqrt(n)*(gammatilde - gamma)
stdgammaexp <- sqrt(n)*(gammatildeexp - gamma)
stdgammabin <- sqrt(n)*(gammatildebin - gamma)
msd <- rep(0, length(s)*2)
dim(msd) <- c(length(s), 2)
msdexp <- rep(0, length(s)*2)
dim(msdexp) <- c(length(s), 2)
msdbin <- rep(0, length(s)*2)
dim(msdbin) <- c(length(s), 2)
for (i in 1:length(s)){
  msd[i,] <- c(mean(stdgammaunif[i,]), (sd(stdgammaunif[i,])/sigmaunif)^2)
  msdexp[i,] <- c(mean(stdgammaexp[i,]), (sd(stdgammaexp[i,])/sigmaexp)^2)
  msdbin[i,] <- c(mean(stdgammabin[i,]), (sd(stdgammabin[i,])/sigmabin)^2)
}

# Right side of Figure 1 in the paper: 

plot(s,msd[,2], type='l', ylim = c(1,5), xlab=expression(italic(s)), ylab = '', cex.axis=1.5, cex.lab=1.5)
points(s, msdbin[,2], type ='l', lty = 2, col = 'red')
points(s, msdexp[,2], type ='l', lty = 3, col = 'blue')
legend("bottomleft", legend=c("Uniform", "Bernoulli","Exponential"),
       col=c("black","red", "blue"),lty=1:3, cex=1.5)



# The $h$ function on the left side of Figure 1 in the paper:

Nx <- 1000
x <- (1:Nx)/Nx
sigma <- x/((1-x)*log(1-x)^2)
plot(x, sigma, type='l', xlab=expression(italic(s)), ylab='', ylim=c(1,5), xlim=c(0.2, 1), cex.lab=1.5,
     cex.axis=1.5)
title(ylab=expression(italic(h(s))), line=2.2, cex.lab=1.5)


###########################################################
## Section 2.3 (i) Hill estimator in the classical iid setting
###########################################################

# In what follows we calculate the classical Hill estimator of the tail index
# when $Q$ is the quantile function of the underlying iid random variables.
# We repeat the simulation $m$ times.

# Q : quantile function
# n : the number iid random variables
# m : number of iterations
# klist: list of k values (upper order statistics used for the estimator)

## We use that conditioned on $U_{k+1,n}$ the first $k$ order statistics are iid
## uniformly distributed on $(0,U_{k+1,n})$.
## Therefore we simulate $U_{k+1,n}$, which is beta(k+1,n-k) distributed,
## then $k$ iid uniform(0,1).

Hillsim <- function(Q, n, m, klist){
  est <- rep(0, m*length(klist))
  dim(est) <- c(m, length(klist))
  # this matrix contains the simulated estimators of the tail index
  for (i in 1:m){
    kmax <- klist[length(klist)]
    Umax <- rbeta(1,kmax+1,n-kmax)
    Usamp <- Umax*runif(kmax)
    us <- c(Usamp[order(Usamp)],Umax)
    for (j in 1:length(klist)){
      k <- klist[j]
      Ukn <- us[(k+1)]
      est[i,j] <- sum((log( Q(us[1:k]) / Q(Ukn)) ))/k 
      # this is the Hill estimator of the $i$th sample, based on $klist[j]$ upper order statistics
      }
    }
  estmean <- rep(0, length(klist))
  for (j in 1:length(klist)){
        estmean[j] <- round(mean(est[,j]),4)
  }
  # estmean contains the average of $m$ iterations
  return(estmean)
}

# Next we calculate coverage frequencies for the asymptotic
# $1 - eps$ confidence intervals. Otherwise, it is the same as above.
# We use two different confidence intervals: (i) suggested by our new model, 
# (ii) classical iid setup. These are formulas (9) and (10) in the paper. 

Hillconfint <- function(Q, n, m, klist, eps = 0.1){
  est <- rep(0, m*length(klist))
  dim(est) <- c(m, length(klist))
  sigma <- rep(0, m*length(klist))
  dim(sigma) <- c(m, length(klist))
  #set.seed(1)
  xeps <- qnorm(1-eps/2)
  count <- 0*1:(length(klist))
  count2 <- 0*1:(length(klist))
  for (i in 1:m){
    kmax <- klist[length(klist)]
    Umax <- rbeta(1,kmax+1,n-kmax)
    Usamp <- Umax*runif(kmax)
    us <- c(Usamp[order(Usamp)],Umax)
    for (j in 1:length(klist)){
      k <- klist[j]
      Ukn <- us[(k+1)]
      est[i,j] <- sum((log( Q(us[1:k]) / Q(Ukn)) ))/k
      sigma[i,j] <- sqrt(sum(((1:k)*log(Q(us[1:k])/Q(us[2:(k+1)])))^2)/k - (est[i,j])^2)
    }
    elem <- which(est[i,] - xeps*sigma[i,]/sqrt(klist) < gamma & gamma < est[i,] + xeps*sigma[i,]/sqrt(klist))
    count[elem] <- count[elem] +1
    elem2 <- which(est[i,] - xeps*est[i,]/sqrt(klist) < gamma & gamma < est[i,] + xeps*est[i,]/sqrt(klist))
    count2[elem2] <- count2[elem2] +1
  }
  estmean <- rep(0, 3*length(klist))
  dim(estmean) <- c(3,length(klist))
  for (j in 1:length(klist)){
    estmean[1, j] <- round(mean(est[,j]),4)
    # average of the $m$ iterations
    estmean[2, ] <- round(count/m, 3)
    estmean[3, ] <- round(count2/m, 3)
    # coverage frequencies of the two confidence intervals
  }
  return(estmean)
}



# In the paper we use two distributions: the exact Pareto, and a small perturbation of it.
# The tail index is $0.5$ in both cases.

# exact Pareto quantile function:
gamma <- 0.5
Q1 <- function(u)
{u^(-gamma)}

# Hall model quantile function:
beta <- 1
d <- 0.5
Q2 <- function(u)
{u^(-gamma)*(1+d*u^(beta))}


# The left side figure in Figure 2 in the paper.
# In this case there is only one sample.

set.seed(1)
a<- Hillsim(Q2, 5000, 1, klist = seq(10, 5000, 10))
b<- Hillsim(Q1, 5000, 1, klist = seq(10, 5000, 10)) ## exact Pareto

plot(seq(10,5000,10), a, type = 'l', xlab=expression(italic(k)), ylab='', 
     ylim = c(0.3, 0.7), cex.lab=1.5, cex.axis=1.5)
title(ylab='Hill estimator', line=2.2, cex.lab=1.5)
points(seq(10,5000,10), b, type = 'l', lty = 2, col = 'red')
legend("topright", legend=c("Hall class", "Pareto"),
       col=c("black","red"),lty=1:2, cex=1.5)



# Confidence intervals. The left side of Figure 3 in the paper.

aPar <- Hillconfint(Q1, 5000, 10000, seq(10, 5000, 10), eps = 0.1)
bHall <- Hillconfint(Q2, 5000, 10000, seq(10, 5000, 10), eps = 0.1)
Sys.time() ## 50 perc

plot(seq(10,5000, 10), aPar[2,], 
     type = 'l', lty = 1, xlab=expression(italic(k)), ylab ='', ylim = c(0.8, 0.92), cex.lab=1.5, cex.axis=1.5)
title(ylab='coverage frequency', line=2.2, cex.lab=1.5)
points(seq(10,5000, 10), aPar[3,], type = 'l', lty = 2, col = 'red')
points(seq(10,5000, 10), bHall[2,], type = 'l', lty = 3, col = 'blue')
points(seq(10,5000, 10), bHall[3,], type = 'l', lty = 4, col = 'green')
legend("bottomright", legend=c("Hall class (9)", "Hall class (10)", "Pareto (9)", "Pareto (10)"),
       col=c("blue", "green","black","red"),lty=c(3,4,1,2), cex=1.5)




###########################################################
## Section 2.3 (ii) Hill estimator in the generalized Rényi model
###########################################################

# The Hill estimator in this case is simply an average of iid
# random variables.
# In the paper we consider 3 distributions: exponential, uniform, and 
# Bernoulli, each with mean $gamma = 0.5$.

gamma <- 0.5 
n <- 5000
#m <- 1000
set.seed(100)
sampleunif <- 2*gamma*runif(n)
samplebin <- rbinom(n, 1, 0.5)
sampleexp <- gamma*rexp(n, rate=1)
unif <- cumsum(sampleunif)
bern <- cumsum(samplebin)
cexp <- cumsum(sampleexp)
estuni <- unif/(1:n)
estbin <- bern/(1:n)
estexp <- cexp/(1:n)



# Right side of Figure 2 in the paper.

plot(1:n, estuni, type = 'l', ylim = c(0.4, 0.6), lty = 1, xlab=expression(italic(k)), ylab='', cex.lab=1.5, cex.axis=1.5)
title(ylab='Hill estimator', line=2.2, cex.lab=1.5)
points(1:n, estbin, type = 'l', lty = 2, col = 'red')
points(1:n, estexp, type = 'l', lty = 3, col = 'blue')
legend("topright", legend=c("Uniform", "Bernoulli","Exponential"),
       col=c("black","red", "blue"),lty=1:3, cex=1.5)


# Coverage frequencies of the asymptotic confidence intervals:

epsilon = 0.1
xeps <- qnorm(0.95)

n <- 5000  # number of iid random variables in one sample
N <- 10000 # number of iterations
countunif <- 0*1:n
countbin <- 0*1:n
countexp <- 0*1:n
set.seed(100)
for (i in 1:N){
  sampleunif <- 2*gamma*runif(n)
  samplebin <- rbinom(n, 1, 0.5)
  sampleexp <- gamma*rexp(n, rate=1)
  unif <- cumsum(sampleunif)
  bern <- cumsum(samplebin)
  cexp <- cumsum(sampleexp)
  estuni <- unif/(1:n)
  estbin <- bern/(1:n)
  estexp <- cexp/(1:n)
  sigmaunif <- sqrt(cumsum(sampleunif^2)/(1:n)-estuni^2) 
  # estimation of the variances 
  sigmabin <- sqrt(cumsum(samplebin^2)/(1:n)-estbin^2) 
  sigmaexp <- sqrt(cumsum(sampleexp^2)/(1:n)-estexp^2) 
  elemunif <- which(estuni - xeps*sigmaunif/sqrt(1:n) < gamma & gamma < estuni + xeps*sigmaunif/sqrt(1:n))
  countunif[elemunif] <- countunif[elemunif] +1
  elembin <- which(estbin - xeps*sigmabin/sqrt(1:n) < gamma & gamma < estbin + xeps*sigmabin/sqrt(1:n))
  countbin[elembin] <- countbin[elembin] +1
  elemexp <- which(estexp - xeps*sigmaexp/sqrt(1:n) < gamma & gamma < estexp + xeps*sigmaexp/sqrt(1:n))
  countexp[elemexp] <- countexp[elemexp] +1
}


# Right side of Figure 3:

plot(seq(10, n, 20),countunif[seq(10, n, 20)]/N, type = 'l', 
     lty = 1, xlab=expression(italic(k)), ylab ='', ylim = c(0.86, 0.92), cex.lab=1.5, cex.axis=1.5)
title(ylab='coverage frequency', line=2.2, cex.lab=1.5)
points(seq(10, n, 20),countbin[seq(10, n, 20)]/N, type = 'l', lty=2, col = 'red')
points(seq(10, n, 10),countexp[seq(10, n, 10)]/N, type = 'l', lty=3, col = 'blue')
legend("bottomright", legend=c("Uniform", "Bernoulli","Exponential"),
       col=c("black","red", "blue"),lty=1:3, cex=1.5)
