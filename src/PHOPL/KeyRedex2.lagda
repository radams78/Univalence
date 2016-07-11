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

