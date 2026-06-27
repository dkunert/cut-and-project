import numpy as np
import pandas as pd
from sklearn.metrics import r2_score, mean_absolute_error
from xgboost import XGBRegressor
from sklearn.model_selection import GridSearchCV
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt
import statsmodels.api as sm


def xgboost(df):
    print("xgboost")

    # Filter the rows for which period > 0 applies and log transform the target variable
    df_positive = df[df['period'] > 0].copy()
    df_positive['log_period'] = np.log10(df_positive['period'])

    # Selection of the predictors and the target variable
    X = df_positive[['o_n', 'o_d', 'a_n', 'a_d']]
    y = df_positive['log_period']

    # Definition of the parameter grid
    param_grid = {
        'n_estimators': [50, 100, 150],
        'max_depth': [3, 4, 5],
        'learning_rate': [0.01, 0.05, 0.1],
        'min_child_weight': [1, 3, 5],
        'subsample': [0.8, 1.0],
        'colsample_bytree': [0.8, 1.0],
        'gamma': [0, 0.1, 0.3]
    }

    # Initialization of the XGBoost regressor
    xgb_model = XGBRegressor(random_state=42)

    # Einrichtung von GridSearchCV: Hier nutzen wir 3-fache Kreuzvalidierung (cv=3)
    grid_search = GridSearchCV(estimator=xgb_model,
                               param_grid=param_grid,
                               scoring='r2',
                               cv=3,
                               verbose=1,
                               n_jobs=-1)

    # Fit of the grid search object to our data
    grid_search.fit(X, y)

    # Output of the best parameters and the associated R**2 score
    print("Best parameters:", grid_search.best_params_)
    print("Best R**2 score:", grid_search.best_score_)


def formular_analysis_linear(df):
    print("formular_analysis_linear")

    # Filter: only rows with period > 0 (thus excluding period = -2)
    # and at the same time we avoid o_d == 0 to prevent division by zero.
    df = df[(df['period'] > 0) & (df['o_d'] != 0)].copy()

    # 2. Calculation of the terms according to the combined approach:
    # term1 = (o_n/o_d) * (a_n + a_d + 1)
    df['term1'] = (df['o_n'] / df['o_d']) * (df['a_n'] + df['a_d'] + 1)

    # term2 = o_n - o_d
    df['term2'] = df['o_n'] - df['o_d']

    # 3. estimation of lambda:
    # We set up the model: period - term1 = lambda * term2.
    # This corresponds to a linear regression without forced zero (but we add a constant here if necessary).
    y = df['period'] - df['term1']
    X = df['term2']
    X = sm.add_constant(X)  # In the event that a small correction term is required
    model = sm.OLS(y, X).fit()
    print(model.summary())

    # The estimate of lambda corresponds to the coefficient of term2.
    lambda_est = model.params['term2']
    print("Estimated Lambda value: ", lambda_est)

    # 4 Calculation of the prediction and evaluation
    df['period_pred'] = df['term1'] + lambda_est * df['term2']

    # Calculation of R**2 and MAE for evaluation
    r2 = r2_score(df['period'], df['period_pred'])
    mae = mean_absolute_error(df['period'], df['period_pred'])
    print("R**2 of the combined model:", r2)
    print("Mean absolute error of the combined model:", mae)

    # Plot: Beobachtete versus vorhergesagte Werte
    plt.figure(figsize=(8, 6))
    plt.scatter(df['period'], df['period_pred'], alpha=0.5, label='data points')
    plt.xlabel("observed period")
    plt.ylabel("predicted period")
    plt.title("observed vs. predicted period")

    # Diagonal line for ideal model
    min_val = df['period'].min()
    max_val = df['period'].max()
    plt.plot([min_val, max_val], [min_val, max_val], 'r--', label='Ideal forecast')
    plt.legend()
    plt.show()


def formular_analysis_sin_offset(df):
    """
    Perform the combined-model analysis with a sinusoidal adjustment term.
    Model: period = term1 + A * sin((o_n - o_d) + V)
    where term1 = (o_n / o_d) * (a_n + a_d + 1).
    Fits A and V via non‑linear least squares.
    """

    print("formular_analysis_sin_offset")

    # 1. Filter DataFrame: keep only rows with period > 0 and o_d != 0
    df = df[(df['period'] > 0) & (df['o_d'] != 0)].copy()

    # 2. Compute term1: (o_n/o_d) * (a_n + a_d + 1)
    df['term1'] = (df['o_n'] / df['o_d']) * (df['a_n'] + df['a_d'] + 1)
    df['term1'] = np.floor(df['term1'])

    # 3. Prepare x (difference) and y (residual to fit)
    x = (df['o_n'] - df['o_d']).values
    y = (df['period'] - df['term1']).values

    # 4. Define the sinusoidal model y = A * sin(x + V)
    def sinus_model(x, A, V):
        return A * np.sin(x + V)

    # 5. Fit the model to estimate parameters A (multiplier) and V (offset)
    popt, _ = curve_fit(sinus_model, x, y, p0=[1.0, 0.0])
    A_opt, V_opt = popt
    print(f"Optimized multiplier A: {A_opt:.6f}")
    print(f"Optimized offset V:     {V_opt:.6f}")

    # 6. Generate predictions using the fitted model
    df['period_pred'] = df['term1'] + sinus_model(x, A_opt, V_opt)

    # 7. Evaluate performance (R**2 and MAE)
    r2 = r2_score(df['period'], df['period_pred'])
    mae = mean_absolute_error(df['period'], df['period_pred'])
    print(f"R**2:  {r2:.6f}")
    print(f"MAE: {mae:.6f}")

    # 8. Plot observed vs. predicted period
    plt.figure(figsize=(8, 6))
    plt.scatter(df['period'], df['period_pred'], alpha=0.5, label='Data points')
    mn, mx = df['period'].min(), df['period'].max()
    plt.plot([mn, mx], [mn, mx], 'r--', label='Ideal fit')
    plt.xlabel("Observed period")
    plt.ylabel("Predicted period")
    plt.title("Observed vs. Predicted period with sin(x + V) term")
    plt.legend()
    plt.show()


def formular_analysis_quad_offset(df):
    """
    Perform the combined-model analysis with a quadratic adjustment term.
    Model:    period = term1 + A * term1 * diff + B * diff^2
    where
      term1 = (o_n / o_d) * (a_n + a_d + 1)
      diff  = o_n - o_d
    Fits A and B via non-linear least squares.
    """

    print("formular_analysis_quad_offset")

    # 1. Filter DataFrame: keep only rows with period > 0 and o_d != 0
    df = df[(df['period'] > 0) & (df['o_d'] != 0)].copy()

    # 2. Compute term1 and diff
    df['term1'] = (df['o_n'] / df['o_d']) * (df['a_n'] + df['a_d'] + 1)
    df['diff'] = df['o_n'] - df['o_d']

    # 3. Prepare xdata (term1, diff) and ydata (period)
    xdata = np.vstack((df['term1'].values, df['diff'].values))
    ydata = df['period'].values

    # 4. Define the model: period_pred = term1 + A * term1 * diff + B * diff^2
    def quad_model(xdata, A, B):
        term1, diff = xdata
        return term1 + A * term1 * diff + B * diff ** 2

    # 5. Fit the model to estimate parameters A and B
    p0 = [0.0, 0.0]  # initial guesses for A and B
    popt, _ = curve_fit(quad_model, xdata, ydata, p0=p0)
    A_opt, B_opt = popt
    print(f"Optimized coefficient A: {A_opt:.6f}")
    print(f"Optimized coefficient B: {B_opt:.6f}")

    # 6. Generate predictions using the fitted model
    df['period_pred'] = quad_model(xdata, A_opt, B_opt)

    # 7. Evaluate performance (R**2 and MAE)
    r2 = r2_score(df['period'], df['period_pred'])
    mae = mean_absolute_error(df['period'], df['period_pred'])
    print(f"R**2:  {r2:.6f}")
    print(f"MAE: {mae:.6f}")

    # 8. Plot observed vs. predicted period
    plt.figure(figsize=(8, 6))
    plt.scatter(df['period'], df['period_pred'], alpha=0.5, label='Data points')
    mn, mx = df['period'].min(), df['period'].max()
    plt.plot([mn, mx], [mn, mx], 'r--', label='Ideal fit')
    plt.xlabel("Observed period")
    plt.ylabel("Predicted period")
    plt.title("Observed vs. Predicted period with quadratic offset term")
    plt.legend()
    plt.show()


if __name__ == "__main__":
    def main():
        df = pd.read_csv("find_pattern_x_max_1000000_70977_lines.csv")
        xgboost(df)
        formular_analysis_linear(df)
        formular_analysis_sin_offset(df)
        formular_analysis_quad_offset(df)

    main()
