\AgdaHide{
\begin{code}
module PHOPL.KeyRedex2 where
\end{code}
}

Let $\SN$ be the set of all strongly normalizing expressions.

\begin{lemma}
\label{lm:SN}
$ $
\begin{enumerate}
\item
\label{lm:SN1}
If $M[x:=N]L_1 \cdots L_n \in \SN$ and $N \in \SN$ then $(\lambda x:A.M)NL_1 \cdots L_n \in \SN$.
\item
\label{lm:SN2}
If $\reff{M[x:=N]N_1 \cdots N_m}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n \in \SN$ and $N \in \SN$ then
$\reff{(\lambda x:A.M)NN_1 \cdots N_m}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n \in \SN$.
\item
\label{lm:SN3}
Suppose that:
\begin{enumerate}
\item
\label{hypi}
$M\{x:=P:N\sim N'\}_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n \in \SN$
\item
$P, N, N' \in \SN$
\item
\label{hypiii}
if $\nf{P} \equiv \reff{L}$ then $\reff{M[x:=L]}_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n \in \SN$.
\end{enumerate}
Then $\reff{\lambda x:A.M}_{N N'} P_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n \in \SN$.
\item
\label{lm:SN4}
If $\reff{M[x:=N]}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n, N_1, N_2, N \in \SN$ then \\
$\reff{\lambda x:A.M}_{N_1 N_2}\reff{N}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n \in \SN$.
\item
\label{lm:SN5}
If $\delta, \phi \in \SN$ then $\reff{\phi}^+ \delta, \reff{\phi}^- \delta \in \SN$.
\end{enumerate}
\end{lemma}

\begin{proof}
We prove part \ref{lm:SN3}; the proofs of the other parts are similar.

The proof is by induction on $P \in \SN$, then $N \in \SN$, then $N' \in \SN$,
then on $M\{x := P : N \sim N' \} \vec{P} \in \SN$.  The following are the possible one-step reductions from
$\reff{\lambda x:A.M}_{N N'} P \vec{P}$:

\begin{description}
\item[$\reff{\lambda x:A.M}_{N N'} P \vec{P} \rightarrow \reff{\lambda x:A.M'}_{N N'} P \vec{P}$, where $M \rightarrow M'$.]
$ $

In this case, the result follows straight from the induction hypothesis, because we have $M \{ x:=P : N \sim N' \} \vec{P} \twoheadrightarrow M' \{ x:=P : N \sim N' \} \vec{P} \in \SN$.
And for any term $L$, if $P \twoheadrightarrow \reff{L}$ then $\reff{M[x:=L]} \vec{P} \rightarrow \reff{M'[x:=L]} \vec{P} \in \SN$.

The case where we reduce $N$, $N'$, $P$, or one of the $P_i$s is similar.
\item[$\reff{\lambda x:A.M}_{N N'} P \vec{P} \rightarrow M \{ x := P : N \sim N' \} \vec{P}$] where $P$ is a closed normal form that is not a $\reff{-}$.

The conclusion follows from hypothesis \ref{hypi}.
\item[$P \equiv \reff{L}$ and $\reff{\lambda x:A.M}_{N N'} \reff{L} \vec{P} \rightarrow \reff{(\lambda x:A.M)L}_{N N'} \vec{P}$]

In this case, we have $\reff{M[x:=L]}\vec{P} \in \SN$ by hypothesis \ref{hypiii}, and the conclusion follows by part \ref{lm:SN2}.
\end{description}
\end{proof}

% \begin{lemma}
% \label{lm:SNrefapp}
% If $\reff{M}_{N_1 N_2} \reff{N}_{K_1 K_1'} P_1 \cdots_{K_n K_n'} P_n \in \SN$ then \\
% $\reff{MN}_{K_1 K_1'} P_1 \cdots_{K_n K_n'} P_n \in \SN$.
% \end{lemma}

% \begin{proof}
% The proof is by induction on the hypothesis.  These are the possible one-step reductions from $\reff{MN} \vec{P}$:

% \begin{description}
% \item[$\reff{MN} \vec{P} \rightarrow \reff{M'N} \vec{P}$ where $M \rightarrow M'$]
% Then we have $\reff{M}_{N_1 N_2} \reff{N} \vec{P} \rightarrow \reff{M'}_{N_1 N_2} \reff{N} \vec{P} \in \SN$, and the result follows by the
% induction hypothesis.  Similarly if we reduce $N$ or one of the $P_i$, $K_i$ or $K_i'$.

% \item[$MN$ is a redex]
% Then $M$ and $N$ are closed normal forms, and so \\
% $\reff{M}_{N_1 N_2} \reff{N} \vec{P} \rightarrow \reff{MN} \vec{P}$, hence
% $\reff{MN} \vec{P} \in \SN$.
% \end{description}
% \end{proof}

\begin{lemma}
\label{lm:SNothers}
$ $
\begin{enumerate}
\item
If $\delta[p:=\epsilon], \phi, \epsilon \in \SN$ then $(\lambda p:\phi.\delta)\epsilon \in \SN$.
\item
If $P[x:=L, y:=L', e:=Q], L, L', Q \in \SN$ then $(\triplelambda e:x =_A y.P)_{L L'} Q \in \SN$.
\end{enumerate}
\end{lemma}

\begin{proof}
Similar to the previous lemmas.
\end{proof}

\begin{lemma}
\label{lm:wte_loi1}
If $(\delta \chi_{L_1 L_1'} \theta_1 \cdots_{L_m L_m'} \theta_m)^+ \alpha \beta_1 \cdots \beta_n \in \SN$ and $\phi, \psi, \epsilon \in \SN$, then
$(\univ{\phi}{\psi}{\delta}{\epsilon}^+ \chi_{L_1 L_1'} \theta_1 \cdots_{L_m L_m'} \theta_m)^+ \alpha \beta_1 \cdots \beta_n \in \SN$.
\end{lemma}

\begin{proof}
Similar.
\end{proof}

\begin{lemma}
\label{lm:wte_loi2}
If $(\delta[p:=\epsilon]_{L_1 L_1'} \theta_1 \cdots_{L_m L_m'} \theta_m)^+ \alpha \beta_1 \cdots \beta_n \in \SN$ and $\phi, \epsilon \in \SN$, then
$((\lambda p:\phi.\delta) \epsilon_{L_1 L_1'} \theta_1 \cdots_{L_m L_m'} \theta_m)^+ \alpha \beta_1 \cdots \beta_n \in \SN$.
\end{lemma}

\begin{proof}
Similar.
\end{proof}

\begin{lemma}
\label{lm:wte_loi3}
If $(\delta[x:=M, y:=N, p:=\epsilon]_{L_1 L_1'} \theta_1 \cdots_{L_m L_m'} \theta_m)^+ \alpha \beta_1 \cdots \beta_n \in \SN$ and $M, N, \epsilon \in \SN$, then
$((\triplelambda p:x =_A y.\delta)_{MN} \epsilon_{L_1 L_1'} \theta_1 \cdots_{L_m L_m'} \theta_m)^+ \alpha \beta_1 \cdots \beta_n \in \SN$.
\end{lemma}

\begin{proof}
Similar.
\end{proof}

\begin{lemma}
\label{lm:SNred1}
If $\reff{M}_{NN} \reff{N}_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n \in \SN$ then \\
$\reff{MN}_{L_1 L_1'} P_1 \cdots_{L_n L_n'} P_n \in \SN$.
\end{lemma}

\begin{proof}
The proof is by induction on the hypothesis.  Consider all possible one-step reductions from $\reff{MN} \vec{P}$.

If $\reff{MN} \vec{P} \rightarrow \reff{MN'} \vec{P}$ where $M \rightarrow M'$, then we have $\reff{M}_{N' N'} \reff{N'} \vec{P} \in \SN$, and so
$\reff{MN'} \vec{P} \in \SN$ by the induction hypothesis.  Similarly for the case where we reduce $M$ or one of the $L_i$, $L_i'$ or $P_i$.

The only other case is is $MN$ is a redex.  In this case, $M$ and $N$ are closed normal forms, and so we have $\reff{M}_{NN} \reff{N} \vec{P} \rightarrow \reff{MN} \vec{P} \in \SN$.
\end{proof}