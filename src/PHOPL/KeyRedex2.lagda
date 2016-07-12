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
If $M[x:=N]L_1 \cdots L_n, N \in \SN$ then $(\lambda x:A.M)NL_1 \cdots L_n \in \SN$.
\item
\label{lm:SN2}
If $\reff{M[x:=N]N_1 \cdots N_m}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n, N \in \SN$ then \\
$\reff{(\lambda x:A.M)NN_1 \cdots N_m}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n \in \SN$.
\item
\label{lm:SN3}
If $M\{x:=P:N\sim N'\}, P, N, N' \in \SN$ and $P$ is not of the form $\reff{-}$, then $\reff{\lambda x:A.M}_{N N'} P \in \SN$.
\item
\label{lm:SN4}
If $\reff{M[x:=N]}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n, N_1, N_2, N \in \SN$ then \\
$\reff{\lambda x:A.M}_{N_1 N_2}\reff{N}_{L_1 L_1'} (P_1)_{L_2 L_2'} \cdots_{L_n L_n'} P_n \in \SN$.
\end{enumerate}
\end{lemma}

\begin{proof}
We prove part 1; the proofs of the other parts are similar.

The proof is by induction on $N \in \SN$, then on $M[x:=N]L_1 \cdots L_n \in \SN$.  The following are the possible one-step reductions from
$(\lambda x:A.M)NL_1 \cdots L_n$.

\begin{description}
\item[$(\lambda x:A.M)N\vec{L} \rightarrow (\lambda x:A.M)N'\vec{L}$, where $N \rightarrow N'$.]
This case follows from the induction hypothesis on $N$.

\item[$(\lambda x:A.M)N\vec{L} \rightarrow (\lambda x:A.M')N\vec{L}$, where $M \rightarrow M'$.]
This case follows from the induction hypothesis on $M[x:=N]\vec{L}$.  Similarly for the case where
we reduce one of the $L_i$.

\item[$(\lambda x:A.M)N\vec{L} \rightarrow M{[x:=N]}\vec{L}$.]  We have $M[x:=N]\vec{L} \in \SN$ by hypothesis.
\end{description}
\end{proof}

\begin{lemma}
\label{lm:SNrefapp}
If $\reff{M}_{N_1 N_2} \reff{N}_{K_1 K_1'} P_1 \cdots_{K_n K_n'} P_n \reff{N} \in \SN$ then \\
$\reff{MN}_{K_1 K_1'} P_1 \cdots_{K_n K_n'} P_n \in \SN$.
\end{lemma}

\begin{proof}
The proof is by induction on the hypothesis.  These are the possible one-step reductions from $\reff{MN} \vec{P}$:

\begin{description}
\item[$\reff{MN} \vec{P} \rightarrow \reff{M'N} \vec{P}$ where $M \rightarrow M'$]
Then we have $\reff{M}_{N_1 N_2} \reff{N} \vec{P} \rightarrow \reff{M'}_{N_1 N_2} \reff{N} \vec{P} \in \SN$, and the result follows by the
induction hypothesis.  Similarly if we reduce $N$ or one of the $P_i$, $K_i$ or $K_i'$.

\item[$MN$ is a redex]
Then $M$ and $N$ are closed normal forms, and so $\reff{M}_{N_1 N_2} \reff{N} \vec{P} \rightarrow \reff{MN} \vec{P}$, hence
$\reff{MN} \vec{P} \in \SN$.
\end{description}
\end{proof}
