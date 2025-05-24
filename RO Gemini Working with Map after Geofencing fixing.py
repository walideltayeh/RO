import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import pandas as pd
import numpy as np
import folium # Requires installation: pip install folium openpyxl
# import webbrowser # Not used directly, folium handles map opening via _open_file_or_folder
from datetime import datetime
import calendar
import os
import xlsxwriter # Requires installation: pip install XlsxWriter (often installed with pandas or openpyxl)
from typing import Dict, List, Tuple, Optional, Any # Ensure Optional is imported
import threading
from queue import Queue, Empty as QueueEmpty # Import Empty exception
import math
# Import OR-Tools routing wrapper
from ortools.constraint_solver import routing_enums_pb2
from ortools.constraint_solver import pywrapcp
# Import top-level ortools package for version checking
import ortools # Requires installation: pip install ortools

# Import for K-Means
from sklearn.cluster import KMeans # Requires: pip install scikit-learn
from sklearn.preprocessing import StandardScaler # For K-Means (optional, but good practice)

import sys
import traceback # For detailed error logging
import subprocess # For opening files/folders
import platform # To check OS for opening files/folders

# --- Helper Function: Haversine Distance ---
def haversine(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    """
    Calculate the great circle distance in kilometers between two points
    on the earth (specified in decimal degrees)
    """
    try:
        # Ensure inputs are floats before proceeding
        f_lat1, f_lon1, f_lat2, f_lon2 = float(lat1), float(lon1), float(lat2), float(lon2)
        # Convert decimal degrees to radians
        lon1_r, lat1_r, lon2_r, lat2_r = map(math.radians, [f_lon1, f_lat1, f_lon2, f_lat2])
    except (TypeError, ValueError, AttributeError):
        # Return NaN if conversion fails (e.g., None, non-numeric string)
        return np.nan

    # Haversine formula
    dlon = lon2_r - lon1_r
    dlat = lat2_r - lat1_r
    a = math.sin(dlat / 2)**2 + math.cos(lat1_r) * math.cos(lat2_r) * math.sin(dlon / 2)**2

    # Handle potential floating point inaccuracies slightly outside [0, 1]
    if a < 0: a = 0.0
    elif a > 1: a = 1.0

    c = 2 * math.asin(math.sqrt(a))
    r = 6371 # Radius of earth in kilometers. Use 3956 for miles
    return c * r

# --- Main Application Class ---
class RouteOptimizationApp:
    def __init__(self):
        self.root = tk.Tk()
        # Updated version number
        self.root.title("Route Optimizer By Waild El Tayeh v2.26 (KMeans & Status Map Fix)")
        self.root.geometry("850x650")
        self.outlets_data: Optional[pd.DataFrame] = None
        self.routes: Dict[int, List[pd.DataFrame]] = {}
        # Schedule structure: Dict[RepName(str), List[DayEntry(Dict)]]
        # DayEntry Dict: {'Week': int, 'Day': str, 'Week Type': str, 'Outlets': List[str], 'Count': int, 'RouteDF': pd.DataFrame}
        self.schedule: Dict[str, List[Dict[str, Any]]] = {}
        self.status_var = tk.StringVar(value="Initializing...") # Update initial status
        self.progress_var = tk.DoubleVar(value=0)
        self.processing = False # Flag to indicate if a background task (opt/export) is running
        self.queue = Queue() # Queue for thread communication
        self.params: Dict[str, Any] = {} # Stores validated parameters
        self.last_export_dir = "" # Stores path of last export for easy access

        # Store integer status codes directly after checking they exist in the expected module
        self.STATUS_MAP = {}
        self.ROUTING_SUCCESS_CODE = 1 # Default
        self.ROUTING_FAIL_TIMEOUT_CODE = 3 # Default

        self.create_widgets() # Create widgets before initializing map
        self._initialize_status_map() # Call initialization AFTER queue exists
        self.layout_widgets()
        self.setup_queue_checker()
        self.status_var.set("Ready") # Set status to Ready after init


    def _initialize_status_map(self):
        """Initialize mapping from integer status code to string representation using default values."""
        # Use log_message for initialization logs - safe because queue exists now
        self.log_message("Initializing OR-Tools Status Map...")

        # Directly use the standard integer codes based on common OR-Tools definitions
        # These integer values are generally stable across versions for the core statuses.
        self.STATUS_MAP = {
            0: 'ROUTING_NOT_SOLVED',    # pywrapcp.RoutingModel.ROUTING_NOT_SOLVED
            1: 'ROUTING_SUCCESS',       # pywrapcp.RoutingModel.ROUTING_SUCCESS
            2: 'ROUTING_FAIL',          # pywrapcp.RoutingModel.ROUTING_FAIL
            3: 'ROUTING_FAIL_TIMEOUT',  # pywrapcp.RoutingModel.ROUTING_FAIL_TIMEOUT
            4: 'ROUTING_INVALID',       # pywrapcp.RoutingModel.ROUTING_INVALID
        }

        # Attempt to get actual constant values if possible, otherwise use defaults
        # This makes the code more resilient to slight API changes in where constants are defined.
        try:
            self.ROUTING_SUCCESS_CODE = pywrapcp.RoutingModel.ROUTING_SUCCESS
            self.ROUTING_FAIL_TIMEOUT_CODE = pywrapcp.RoutingModel.ROUTING_FAIL_TIMEOUT
            self.log_message("Successfully loaded status codes from pywrapcp.RoutingModel.")
        except AttributeError:
            self.log_message("Warning: Could not load status codes from pywrapcp.RoutingModel. Using default integer values.")
            # Defaults are already set, so no further action needed for codes here.

        # For the STATUS_MAP, ensure it's populated even if direct attribute access fails
        # by checking against the default integers if names weren't found.
        temp_map = {}
        status_defs = {
            'ROUTING_NOT_SOLVED': 0, 'ROUTING_SUCCESS': 1, 'ROUTING_FAIL': 2,
            'ROUTING_FAIL_TIMEOUT': 3, 'ROUTING_INVALID': 4
        }
        for name, default_int_val in status_defs.items():
            # Try to get the actual integer value of the constant by its name
            actual_int_val = getattr(pywrapcp.RoutingModel, name, None)
            if actual_int_val is None: # If not in RoutingModel, try routing_enums_pb2
                 actual_int_val = getattr(routing_enums_pb2, name, None)

            if actual_int_val is not None:
                temp_map[actual_int_val] = name
            else: # If still not found, use the default integer
                if default_int_val not in temp_map: # Avoid overwriting if already mapped by another constant name
                    temp_map[default_int_val] = name + " (Default Int)"
                self.log_message(f"Warning: OR-Tools status constant '{name}' not found. Using default mapping.")
        self.STATUS_MAP = temp_map

        self.log_message(f"Final OR-Tools Status Map: {self.STATUS_MAP}")
        self.log_message(f"Using ROUTING_SUCCESS code: {self.ROUTING_SUCCESS_CODE}")
        self.log_message(f"Using ROUTING_FAIL_TIMEOUT code: {self.ROUTING_FAIL_TIMEOUT_CODE}")


    def create_widgets(self):
        # Parameter Frame
        self.param_frame = ttk.LabelFrame(self.root, text="Parameters", padding="10")
        self.min_outlets_var = tk.StringVar(value="8")
        self.max_outlets_var = tk.StringVar(value="12")
        self.working_days_var = tk.StringVar(value="5")
        self.solver_time_limit_var = tk.StringVar(value="30")

        ttk.Label(self.param_frame, text="Min outlets per day:").grid(row=0, column=0, padx=5, pady=5, sticky="w")
        self.min_outlets_entry = ttk.Entry(self.param_frame, textvariable=self.min_outlets_var, state='normal', width=10)
        self.min_outlets_entry.grid(row=0, column=1, padx=5, pady=5)

        ttk.Label(self.param_frame, text="Max outlets per day:").grid(row=1, column=0, padx=5, pady=5, sticky="w")
        self.max_outlets_entry = ttk.Entry(self.param_frame, textvariable=self.max_outlets_var, state='disabled', width=10)
        self.max_outlets_entry.grid(row=1, column=1, padx=5, pady=5)

        ttk.Label(self.param_frame, text="Working days per week:").grid(row=2, column=0, padx=5, pady=5, sticky="w")
        self.working_days_entry = ttk.Entry(self.param_frame, textvariable=self.working_days_var, state='disabled', width=10)
        self.working_days_entry.grid(row=2, column=1, padx=5, pady=5)

        ttk.Label(self.param_frame, text="Solver Time Limit (sec):").grid(row=3, column=0, padx=5, pady=5, sticky="w")
        self.solver_time_limit_entry = ttk.Entry(self.param_frame, textvariable=self.solver_time_limit_var, state='disabled', width=10)
        self.solver_time_limit_entry.grid(row=3, column=1, padx=5, pady=5)

        # Add validation traces to update widget states dynamically
        self.min_outlets_var.trace_add("write", self.validate_inputs)
        self.max_outlets_var.trace_add("write", self.validate_inputs)
        self.working_days_var.trace_add("write", self.validate_inputs)
        self.solver_time_limit_var.trace_add("write", self.validate_inputs)

        # Button Frame
        self.button_frame = ttk.Frame(self.root, padding="10")
        self.load_button = ttk.Button(self.button_frame, text="Load Data", command=self.load_data, state='disabled')
        self.optimize_button = ttk.Button(self.button_frame, text="Optimize Routes", command=self.start_optimization, state='disabled')
        self.export_button = ttk.Button(self.button_frame, text="Export Results", command=self.start_export, state='disabled')

        # Progress Frame
        self.progress_frame = ttk.Frame(self.root, padding="5")
        self.progress_bar = ttk.Progressbar(self.progress_frame, variable=self.progress_var, maximum=100, mode='determinate', length=400)

        # Status Bar
        self.status_bar = ttk.Label(self.root, textvariable=self.status_var, relief=tk.SUNKEN, anchor='w', padding=(5, 2))

        # Results/Log Frame
        self.results_frame = ttk.LabelFrame(self.root, text="Log", padding="10")
        self.results_text = tk.Text(self.results_frame, height=20, width=90, wrap=tk.WORD, state='disabled', font=("Courier New", 9))
        self.scrollbar = ttk.Scrollbar(self.results_frame, orient="vertical", command=self.results_text.yview)
        self.results_text.configure(yscrollcommand=self.scrollbar.set)

        # Initial validation call to set initial widget states correctly
        self.validate_inputs()

    def layout_widgets(self):
        self.param_frame.pack(fill=tk.X, padx=10, pady=5)
        self.button_frame.pack(fill=tk.X, padx=10, pady=5)
        self.load_button.pack(side=tk.LEFT, padx=5)
        self.optimize_button.pack(side=tk.LEFT, padx=5)
        self.export_button.pack(side=tk.LEFT, padx=5)
        self.progress_frame.pack(fill=tk.X, padx=10, pady=5)
        self.progress_bar.pack(fill=tk.X)
        self.results_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        self.results_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X, padx=0, pady=0)

    def validate_inputs(self, *args):
        """Validates parameter entries sequentially and sets widget states (entries and Load button)."""
        valid_min, valid_max, valid_days, valid_time = False, False, False, False
        min_val, max_val = 0, 0
        try:
            # Validate Min Outlets
            try: min_val_str = self.min_outlets_var.get(); min_val = int(min_val_str); valid_min = min_val > 0
            except (ValueError, tk.TclError): valid_min = False
            # Enable/Disable Max entry based on Min validity
            if hasattr(self, 'max_outlets_entry') and self.max_outlets_entry.winfo_exists():
                self.max_outlets_entry.config(state='normal' if valid_min else 'disabled')

            # Validate Max Outlets (only if min is valid)
            if valid_min:
                try: max_val_str = self.max_outlets_var.get(); max_val = int(max_val_str); valid_max = max_val >= min_val
                except (ValueError, tk.TclError): valid_max = False
            else: valid_max = False
            if not valid_max: valid_days, valid_time = False, False # Reset subsequent states if max is invalid

            # Validate Working Days (only if max is valid)
            if hasattr(self, 'working_days_entry') and self.working_days_entry.winfo_exists():
                self.working_days_entry.config(state='normal' if valid_max else 'disabled')
            if valid_max:
                try: days_val_str = self.working_days_var.get(); days_val = int(days_val_str); valid_days = 0 < days_val <= 7
                except (ValueError, tk.TclError): valid_days = False
            else: valid_days = False
            if not valid_days: valid_time = False # Reset subsequent states if days is invalid

            # Validate Solver Time (only if days is valid)
            if hasattr(self, 'solver_time_limit_entry') and self.solver_time_limit_entry.winfo_exists():
                self.solver_time_limit_entry.config(state='normal' if valid_days else 'disabled')
            if valid_days:
                try: time_val_str = self.solver_time_limit_var.get(); time_val = int(time_val_str); valid_time = time_val > 0
                except (ValueError, tk.TclError): valid_time = False
            else: valid_time = False

            # Set Load Button State based on all parameter validations
            all_params_valid = valid_min and valid_max and valid_days and valid_time
            new_load_button_state = 'normal' if all_params_valid else 'disabled'
            if hasattr(self, 'load_button') and self.load_button.winfo_exists():
                 if self.load_button.cget('state') != new_load_button_state:
                     self.load_button.config(state=new_load_button_state)

            # If parameters become invalid, disable Optimize/Export (if not already processing)
            # Note: enable_buttons() handles enabling these based on data/results *after* processing
            if not all_params_valid and not self.processing:
                 if hasattr(self, 'optimize_button') and self.optimize_button.winfo_exists():
                     self.optimize_button.config(state='disabled')
                 if hasattr(self, 'export_button') and self.export_button.winfo_exists():
                     self.export_button.config(state='disabled')
        except Exception as e:
             # Use log_message for errors during validation too
             self.log_message(f"Warning: Error during input validation: {e}")

    def load_data(self):
        """Loads data from CSV or Excel, validates, cleans, and updates GUI state."""
        try:
            # Ask user for file
            filename = filedialog.askopenfilename(
                title="Select Outlet Data File",
                filetypes=[("Excel files", "*.xlsx"), ("CSV files", "*.csv"), ("All files", "*.*")]
            )
            if not filename:
                self.log_message("Data loading cancelled by user.")
                return

            self.queue.put(('status', "Loading data file..."))
            self.queue.put(('progress', 10))
            self.log_message(f"Attempting to load data file: {filename}")

            # Specify dtype for crucial columns to read as string initially for better cleaning control
            read_opts = {'dtype': {'latitude': str, 'longitude': str, 'vf': str, 'outletname': str}}
            if filename.lower().endswith('.xlsx'):
                 try:
                     df = pd.read_excel(filename, engine='openpyxl', **read_opts)
                 except Exception as read_err:
                     raise ValueError(f"Failed to read Excel file '{os.path.basename(filename)}'. Ensure it's not corrupted or password-protected. Error: {read_err}")
            elif filename.lower().endswith('.csv'):
                 try:
                     # Try detecting separator, fall back to comma
                     df = pd.read_csv(filename, sep=None, engine='python', **read_opts) # 'python' engine handles sep=None better
                 except Exception as read_err:
                     raise ValueError(f"Failed to read CSV file '{os.path.basename(filename)}'. Check formatting and encoding. Error: {read_err}")
            else:
                 raise ValueError(f"Unsupported file type: {os.path.splitext(filename)[1]}. Please select a .xlsx or .csv file.")

            if df.empty:
                raise ValueError("The selected file is empty or could not be read properly.")

            # --- Data Cleaning and Validation ---
            # Standardize column names (lowercase, strip spaces) immediately
            df.columns = df.columns.str.lower().str.strip().str.replace(' ', '_') # Also replace spaces with underscores
            self.outlets_data = df
            self.log_message(f"Initial rows loaded: {len(self.outlets_data)}")

            self.validate_data_columns() # Check if required columns exist after standardization

            # Convert crucial columns to numeric, coercing errors to NaN
            cols_to_numeric = ['latitude', 'longitude', 'vf']
            for col in cols_to_numeric:
                original_nan_count = self.outlets_data[col].isnull().sum() # Count NaNs before conversion (includes empty strings from read)
                self.outlets_data[col] = pd.to_numeric(self.outlets_data[col], errors='coerce')
                final_nan_count = self.outlets_data[col].isnull().sum()
                new_nans = final_nan_count - original_nan_count
                if new_nans > 0:
                    self.log_message(f"Warning: Found {new_nans} non-numeric value(s) in column '{col}', converted to NaN.")

            # Drop rows with NaN in essential numeric columns (latitude, longitude, vf)
            initial_len = len(self.outlets_data)
            self.outlets_data.dropna(subset=cols_to_numeric, inplace=True)
            dropped_numeric_nan = initial_len - len(self.outlets_data)
            if dropped_numeric_nan > 0:
                self.log_message(f"Dropped {dropped_numeric_nan} rows due to missing or invalid numeric data in latitude, longitude, or VF.")

            # Convert VF to integer AFTER dropping NaNs
            self.outlets_data['vf'] = self.outlets_data['vf'].astype(int)

            # Validate VF values (must be 2 or 4)
            invalid_vf_mask = ~self.outlets_data['vf'].isin([2, 4])
            if invalid_vf_mask.any():
                dropped_vf_count = invalid_vf_mask.sum()
                self.log_message(f"Warning: Found {dropped_vf_count} rows with invalid VF values (not 2 or 4). Rows dropped.")
                self.outlets_data = self.outlets_data[~invalid_vf_mask].copy() # Keep only valid rows

            # Validate Latitude/Longitude ranges AFTER ensuring they are numeric
            invalid_lat_mask = (self.outlets_data['latitude'] < -90) | (self.outlets_data['latitude'] > 90)
            invalid_lon_mask = (self.outlets_data['longitude'] < -180) | (self.outlets_data['longitude'] > 180)
            invalid_coords_mask = invalid_lat_mask | invalid_lon_mask
            if invalid_coords_mask.any():
                dropped_coord_count = invalid_coords_mask.sum()
                self.log_message(f"Warning: Found {dropped_coord_count} rows with Latitude/Longitude values outside valid ranges. Rows dropped.")
                self.outlets_data = self.outlets_data[~invalid_coords_mask].copy()

            # Validate Outlet Name (must exist and not be empty/whitespace)
            if 'outletname' not in self.outlets_data.columns:
                raise ValueError("Missing required column: 'outletname'") # Should be caught by validate_data_columns earlier

            self.outlets_data['outletname'] = self.outlets_data['outletname'].astype(str).str.strip()
            missing_name_mask = self.outlets_data['outletname'] == ''
            if missing_name_mask.any():
                dropped_name_count = missing_name_mask.sum()
                self.log_message(f"Warning: Found {dropped_name_count} rows with missing or empty 'outletname'. Rows dropped.")
                self.outlets_data = self.outlets_data[~missing_name_mask].copy()


            # Final check if data is empty after all cleaning
            if self.outlets_data.empty:
                raise ValueError("No valid outlet data remains after cleaning and validation.")

            # Handle duplicate outlet names (case-insensitive, using the cleaned name)
            self.outlets_data['outletname_std'] = self.outlets_data['outletname'].str.upper() # Use already stripped name
            num_duplicates = self.outlets_data.duplicated(subset=['outletname_std'], keep=False).sum()
            if num_duplicates > 0:
                 unique_dup_names = self.outlets_data[self.outlets_data.duplicated(subset=['outletname_std'], keep=False)]['outletname_std'].nunique()
                 self.log_message(f"Warning: Found {num_duplicates} rows corresponding to {unique_dup_names} duplicate outlet names (case-insensitive). Keeping the first occurrence of each unique name.")
                 self.outlets_data = self.outlets_data.drop_duplicates(subset=['outletname_std'], keep='first').reset_index(drop=True)
                 self.log_message(f"Removed duplicates, {len(self.outlets_data)} unique outlets remain.")
            self.outlets_data = self.outlets_data.drop(columns=['outletname_std']) # Remove temporary column

            # Log final data summary
            total_outlets = len(self.outlets_data)
            vf2_count = (self.outlets_data['vf'] == 2).sum()
            vf4_count = (self.outlets_data['vf'] == 4).sum()
            self.log_message(f"\n--- Data Analysis Complete (Post-Cleaning) ---")
            self.log_message(f"Total Valid Unique Outlets: {total_outlets}")
            self.log_message(f"  - VF=2: {vf2_count}")
            self.log_message(f"  - VF=4: {vf4_count}")
            self.log_message("-" * 45)

            # Reset previous results and update GUI state
            self.routes = {}
            self.schedule = {}
            self.enable_buttons() # Enables optimize if params are valid
            if hasattr(self, 'export_button') and self.export_button.winfo_exists():
                self.export_button.config(state='disabled') # Export is always disabled after loading new data

            self.log_message("Data loaded, cleaned, and validated successfully.")
            self.queue.put(('status', "Data Loaded. Ready to optimize."))
            self.queue.put(('progress', 100))

        except (FileNotFoundError, pd.errors.EmptyDataError, ValueError, KeyError, TypeError) as e:
            error_msg = f"ERROR loading or validating data: {type(e).__name__}: {e}"
            self.log_message(error_msg) # Log the specific error
            self.queue.put(('error', f"Data Load/Validation Error: {e}")) # Show user-friendly error
            self.outlets_data = None # Clear potentially bad data
            self.routes = {}; self.schedule = {} # Clear results
            self.queue.put(('status', "Data loading failed. Please check file and log."))
            self.queue.put(('progress', 0))
            self.disable_buttons() # Disable all action buttons
            self.validate_inputs() # Re-validate parameters to correctly set Load button state

        except Exception as e:
            # Catch any other unexpected errors during loading/validation
            error_msg = f"Unexpected error during data loading/processing: {type(e).__name__}: {e}\n{traceback.format_exc()}"
            self.log_message(error_msg)
            self.queue.put(('error', f"Load Failed: An unexpected error occurred. Check log for details."))
            self.outlets_data = None
            self.routes = {}; self.schedule = {}
            self.queue.put(('status', "Data loading failed unexpectedly. Check log."))
            self.queue.put(('progress', 0))
            self.disable_buttons()
            self.validate_inputs()

    def validate_data_columns(self):
        """Checks if the required columns exist in the loaded DataFrame after standardization."""
        if self.outlets_data is None: raise ValueError("No data loaded to validate columns.")
        # Check against standardized column names
        required = {'outletname', 'latitude', 'longitude', 'vf'}
        found = set(self.outlets_data.columns)
        missing = required - found
        if missing:
            # Provide a more helpful message showing found columns
            raise ValueError(f"Missing required columns after standardization: {', '.join(missing)}. Found columns: {', '.join(sorted(list(found)))}")
        self.log_message("Required columns (outletname, latitude, longitude, vf) found.")

    def start_optimization(self):
        """Initiates the route optimization process in a background thread."""
        if self.processing:
            self.log_message("Optimization request ignored: Another process is currently running.")
            messagebox.showwarning("Busy", "Optimization or Export is already in progress. Please wait.", parent=self.root)
            return
        if self.outlets_data is None:
            messagebox.showerror("Error", "No data loaded. Please load outlet data first.", parent=self.root)
            return
        if self.outlets_data.empty:
            messagebox.showerror("Error", "Loaded data contains no valid outlets after cleaning.", parent=self.root)
            return
        if not self.validate_parameters():
            messagebox.showerror("Error", "Invalid parameters entered. Please check the parameter values.", parent=self.root)
            return

        # Set processing flag and update GUI
        self.processing = True
        self.disable_buttons() # Disable UI elements during processing
        self.log_message("\n" + "="*15 + " Starting Route Optimization " + "="*15)
        self.progress_var.set(0)
        self.status_var.set("Initializing optimization...")

        # Clear previous results before starting new optimization
        self.routes = {}
        self.schedule = {}

        # Start the optimization task in a separate thread to keep GUI responsive
        threading.Thread(target=self.optimize_routes_task, daemon=True).start()

    def validate_parameters(self) -> bool:
        """Validates parameter values from the UI entries and stores them if valid."""
        try:
            min_o = int(self.min_outlets_var.get())
            max_o = int(self.max_outlets_var.get())
            wd = int(self.working_days_var.get())
            tl = int(self.solver_time_limit_var.get())

            # Perform range checks
            if not (min_o > 0): raise ValueError("Minimum outlets must be greater than 0.")
            if not (max_o >= min_o): raise ValueError("Maximum outlets must be greater than or equal to minimum outlets.")
            if not (0 < wd <= 7): raise ValueError("Working days must be between 1 and 7.")
            if not (tl > 0): raise ValueError("Solver time limit must be greater than 0 seconds.")

            # Store valid parameters in the instance variable
            self.params = {
                'min_outlets': min_o,
                'max_outlets': max_o,
                'working_days': wd,
                'time_limit': tl
            }
            # Log validation success only if all checks pass
            # self.log_message(f"Parameters validated: Min={min_o}, Max={max_o}, Days={wd}, TimeLimit={tl}s") # Logged within enable_buttons or when starting opt
            return True
        except (ValueError, TypeError, tk.TclError) as e:
            # Log the specific validation error
            self.log_message(f"ERROR validating parameters: {e}. Please enter valid positive integers in the correct ranges.")
            # Clear stored params if validation fails
            self.params = {}
            return False

    def optimize_routes_task(self):
        """Worker thread function for the entire optimization process (clustering, VRP, scheduling)."""
        try:
            if self.outlets_data is None or self.outlets_data.empty:
                raise ValueError("Optimization task cannot start: No valid outlet data is loaded.")

            # Log validated parameters being used for this run
            if not self.validate_parameters(): # Re-validate just before use
                 raise ValueError("Optimization stopped: Invalid parameters detected before starting.")
            self.log_message(f"Starting optimization with parameters: Min={self.params['min_outlets']}, Max={self.params['max_outlets']}, Days={self.params['working_days']}, TimeLimit={self.params['time_limit']}s")


            self.queue.put(('status', "Calculating required representatives..."))
            self.queue.put(('progress', 5))
            required_reps = self.calculate_required_reps()

            # Handle calculation failure or zero reps result
            if required_reps is None:
                raise ValueError("Failed to calculate the required number of representatives. Check logs.")
            if required_reps < 0:
                raise ValueError("Calculation resulted in a negative number of representatives. Check input data and parameters.")
            if required_reps == 0:
                 self.log_message("Optimization stopped: Calculation indicates 0 representatives are needed based on workload and parameters.")
                 self.queue.put(('status', "Complete: 0 representatives required."))
                 self.queue.put(('progress', 100))
                 # No 'finally' here, need completion signal
                 self.queue.put(('complete', 'optimization')) # Signal completion
                 return # Exit the task cleanly

            self.queue.put(('status', "Clustering outlets...")) # Updated status
            self.queue.put(('progress', 15))

            # *** Use K-Means for clustering ***
            self.cluster_outlets_kmeans(required_reps) # This will add 'cluster' column

            # Validate clustering results
            if 'cluster' not in self.outlets_data.columns:
                 raise ValueError("Clustering failed: 'cluster' column not added to data.")
            if not pd.api.types.is_integer_dtype(self.outlets_data['cluster']):
                raise TypeError("Clustering assignment resulted in non-integer cluster IDs.")
            if self.outlets_data['cluster'].isnull().any():
                raise ValueError("Clustering failed: Some outlets were not assigned a cluster (resulted in NaN).")

            self.log_message(f"Successfully assigned {len(self.outlets_data)} outlets to {required_reps} clusters using K-Means.")
            cluster_counts = self.outlets_data['cluster'].value_counts().sort_index()
            self.log_message("Cluster sizes summary (K-Means):")
            for c_id, count in cluster_counts.items():
                 self.log_message(f"  - Rep {c_id + 1}: {count} outlets") # K-Means labels are 0-indexed
            if (cluster_counts == 0).any():
                empty_clusters = [c + 1 for c in cluster_counts[cluster_counts == 0].index]
                self.log_message(f"Warning: Clusters {empty_clusters} are empty after K-Means assignment.")

            # --- Generate Routes using VRP Solver ---
            self.queue.put(('status', "Generating optimized routes per cluster..."))
            self.queue.put(('progress', 30))
            self.routes = {} # Reset routes dictionary
            self.routes = self.create_optimized_routes_for_clusters(required_reps)

            if not self.routes:
                 self.log_message("Warning: No routes were generated by the VRP solver for any representative.")
                 # Continue to schedule creation, it should handle empty routes
            elif all(not route_list for route_list in self.routes.values()):
                 self.log_message("Warning: Route generation finished, but all representative route lists are empty.")


            # --- Create Schedule ---
            self.queue.put(('status', "Creating 4-week schedule from routes..."))
            self.queue.put(('progress', 85))
            self.schedule = {} # Reset schedule dictionary
            self.create_schedule() # This function logs its own success/failure

            # Final status update based on schedule content
            schedule_generated = isinstance(self.schedule, dict) and self.schedule and any(bool(e) for e in self.schedule.values())
            if schedule_generated:
                 schedule_reps = len(self.schedule)
                 self.log_message(f"Optimization Task: Schedule successfully created for {schedule_reps} representative(s).")
                 self.queue.put(('status', "Optimization successful. Ready to Export."))
            else:
                 self.log_message("Optimization Task: Schedule generation failed or resulted in an empty schedule.")
                 # Check if the failure was due to lack of routes vs. other scheduling errors
                 if not self.routes or all(not route_list for route_list in self.routes.values()):
                     self.queue.put(('warning', "No schedule could be generated because no routes were planned."))
                 else:
                     self.queue.put(('warning', "No schedule could be generated. Check scheduling logic logs."))
                 self.queue.put(('status', "Optimization complete (No schedule generated)."))


            self.log_message("="*15 + " Optimization Process Complete " + "="*15)
            self.queue.put(('progress', 100))

        except (ValueError, TypeError, Exception) as e:
            # Catch any error during the optimization process
            error_msg = f"ERROR during optimization task: {type(e).__name__}: {e}\n{traceback.format_exc()}"
            self.log_message(error_msg)
            self.queue.put(('error', f"Optimization failed: {type(e).__name__}: {e}")) # Send error to GUI
            self.queue.put(('status', "Optimization failed. Check log for details."))
            self.queue.put(('progress', 0)) # Reset progress bar on error

        finally:
            # This block always runs, ensuring the 'complete' signal is sent
            self.queue.put(('complete', 'optimization')) # Signal task completion to queue checker

    def cluster_outlets_kmeans(self, num_clusters: int):
        """Clusters outlets into num_clusters using K-Means based on latitude and longitude."""
        if self.outlets_data is None or self.outlets_data.empty:
            self.log_message("K-Means Clustering: No outlet data to cluster.")
            return
        if num_clusters <= 0:
            self.log_message(f"K-Means Clustering: Invalid number of clusters ({num_clusters}). Cannot cluster.")
            # Assign all to cluster 0 or handle as error? For now, log and return
            self.outlets_data['cluster'] = 0 # Fallback, or raise error
            return

        # Prepare data for K-Means (latitude, longitude)
        coords = self.outlets_data[['latitude', 'longitude']].copy()

        # K-Means can be sensitive to feature scaling, especially if lat/lon ranges differ significantly
        # Although for lat/lon, the ranges are usually somewhat comparable.
        # scaler = StandardScaler()
        # scaled_coords = scaler.fit_transform(coords)
        # Using raw coordinates is often fine for geographical data with K-Means if clusters are reasonably distinct.
        # If results are poor, scaling could be re-introduced.
        scaled_coords = coords.values # Use .values for KMeans input

        if num_clusters >= len(self.outlets_data):
             self.log_message(f"K-Means: Number of clusters ({num_clusters}) >= number of outlets ({len(self.outlets_data)}). Assigning each outlet to a unique cluster.")
             self.outlets_data['cluster'] = np.arange(len(self.outlets_data))
             return

        try:
            self.log_message(f"Performing K-Means clustering for {num_clusters} clusters...")
            kmeans = KMeans(n_clusters=num_clusters, random_state=42, n_init='auto') # n_init='auto' is default in newer scikit-learn
            self.outlets_data['cluster'] = kmeans.fit_predict(scaled_coords)
            self.log_message(f"K-Means clustering complete. Cluster labels added.")
            # Log centroids for interest
            # cluster_centers = scaler.inverse_transform(kmeans.cluster_centers_) if using scaler
            cluster_centers = kmeans.cluster_centers_
            for i, center in enumerate(cluster_centers):
                self.log_message(f"  Cluster {i} centroid (Lat, Lon): {center[0]:.4f}, {center[1]:.4f}")

        except Exception as e:
            self.log_message(f"ERROR during K-Means clustering: {e}\n{traceback.format_exc()}")
            self.queue.put(('error', f"K-Means Clustering Failed: {e}"))
            # Fallback to assigning all to cluster 0 to prevent downstream errors
            self.outlets_data['cluster'] = 0
            self.log_message("K-Means failed. Assigning all outlets to cluster 0 as a fallback.")


    def calculate_required_reps(self) -> Optional[int]:
        """Calculates the estimated number of representatives needed based on workload."""
        try:
            if self.outlets_data is None or self.outlets_data.empty:
                self.queue.put(('error',"Representative Calculation Error: No outlet data available."))
                self.log_message("ERROR: Cannot calculate representatives, outlet data is missing or empty.")
                return None

            # Get validated parameters
            p = self.params
            min_o = p.get('min_outlets')
            max_o = p.get('max_outlets')
            wd = p.get('working_days')

            # Double-check parameters retrieved (should be valid if validate_parameters passed)
            if not all(isinstance(v, int) and v > 0 for v in [min_o, max_o, wd] if v is not None) or (min_o is not None and max_o is not None and max_o < min_o) :
                 err_msg = f"Representative Calculation Error: Invalid parameters retrieved (Min={min_o}, Max={max_o}, WD={wd})."
                 self.queue.put(('error', err_msg))
                 self.log_message(f"ERROR: {err_msg}")
                 return None

            # --- Calculation Logic ---
            total_outlets = len(self.outlets_data)
            vf4_count = (self.outlets_data['vf'] == 4).sum()
            vf2_count = total_outlets - vf4_count # Assumes only VF 2 and 4 exist after cleaning

            # Total visits needed over a 2-week cycle (VF4 visited twice, VF2 once)
            total_visits_needed_2_weeks = (vf4_count * 2) + vf2_count

            # Average visits a single representative can handle in a 2-week cycle
            avg_outlets_per_day = (min_o + max_o) / 2.0
            visits_per_rep_2_weeks = avg_outlets_per_day * wd * 2.0 # visits/day * days/week * 2 weeks

            # Handle division by zero case
            if visits_per_rep_2_weeks <= 0:
                err_msg = f"Representative Calculation Error: Calculated visits per rep is zero or negative ({visits_per_rep_2_weeks:.1f}). Check parameters (Min/Max outlets, Working days)."
                self.queue.put(('error', err_msg))
                self.log_message(f"ERROR: {err_msg}")
                return None

            # Calculate required reps (ceiling division)
            required_reps = math.ceil(total_visits_needed_2_weeks / visits_per_rep_2_weeks)
            # --- End Calculation ---


            self.log_message(f"\n--- Representative Calculation ---")
            self.log_message(f"Total Unique Outlets: {total_outlets} (VF4={vf4_count}, VF2={vf2_count})")
            self.log_message(f"Total Visits Required (over 2 weeks): {total_visits_needed_2_weeks}")
            self.log_message(f"Avg. Visits per Rep (over 2 weeks): {visits_per_rep_2_weeks:.1f} (based on avg {avg_outlets_per_day:.1f} outlets/day)")
            self.log_message(f"==> Estimated Required Representatives: {required_reps}")
            self.log_message("-" * 30)

            # Sanity check warning
            if required_reps == 0 and total_visits_needed_2_weeks > 0:
                 warning_msg = "Calculation resulted in 0 representatives, but visits are required. This might indicate very high capacity per rep or low visit frequency needs. Proceeding with 0 reps."
                 self.log_message(f"Warning: {warning_msg}")
                 self.queue.put(('warning', warning_msg))

            return int(required_reps)

        except Exception as e:
            # Catch any unexpected errors during calculation
            error_msg = f"Unexpected error during representative calculation: {e}\n{traceback.format_exc()}"
            self.log_message(error_msg)
            self.queue.put(('error', f"Representative Calculation Error: {e}"))
            return None

    # cartesian_to_polar and cluster_by_angle are no longer directly used by optimize_routes_task
    # but might be useful for other analyses or alternative clustering. Keep them for now.
    def cartesian_to_polar(self, coords: np.ndarray, centroid: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """Converts Cartesian coordinates (lat/lon pairs) to polar (angle/radius) relative to a centroid."""
        # Ensure input is numpy array
        coords = np.asarray(coords)
        centroid = np.asarray(centroid)

        # Calculate difference vector from centroid
        delta = coords - centroid

        # Calculate radius (magnitude of delta vector) - uses Euclidean distance approximation
        radius = np.linalg.norm(delta, axis=1)

        # Calculate angle using arctan2 for correct quadrant (-pi to pi)
        # Assumes axis 1 is longitude-like (x) and axis 0 is latitude-like (y) for angle calculation
        angle_rad = np.arctan2(delta[:, 0], delta[:, 1]) # atan2(y, x) -> atan2(lat_delta, lon_delta)

        # Convert angle to degrees (-180 to 180)
        angle_deg = np.degrees(angle_rad)

        # Normalize angle to 0-360 degrees range
        angle_normalized = (angle_deg + 360) % 360

        return angle_normalized, radius

    def cluster_by_angle(self, angles: pd.Series, num_clusters: int) -> pd.Series:
        """Clusters data points into N groups based on their angular position (0-360)."""
        if num_clusters <= 0:
            self.log_message("Warning: Cannot cluster with 0 or negative clusters requested.")
            # Return an empty series or series of NaNs with the same index
            return pd.Series(index=angles.index, dtype=np.int64) # Use numpy int type

        if angles.empty:
            self.log_message("Warning: No angles provided for clustering.")
            return pd.Series(dtype=np.int64)

        n_points = len(angles)
        if num_clusters >= n_points:
            # Assign each point to its own cluster if more clusters requested than points
            self.log_message(f"Warning: Number of clusters ({num_clusters}) >= number of points ({n_points}). Assigning each point to a unique cluster based on sorted angle.")
            sorted_indices = angles.sort_values().index
            cluster_map = {idx: i for i, idx in enumerate(sorted_indices)}
            # Reindex to match original angles Series index order
            return pd.Series(cluster_map).reindex(angles.index).astype(np.int64)

        # Sort points by angle to group them spatially
        sorted_indices = angles.sort_values().index

        # Use np.array_split to divide the *indices* of the sorted points into num_clusters chunks
        # This ensures contiguous angular segments are grouped together.
        split_indices_arrays = np.array_split(np.arange(n_points), num_clusters)

        # Create the cluster assignment series with the original index
        cluster_assignments = pd.Series(index=angles.index, dtype=np.int64) # Initialize with correct type

        # Assign cluster ID based on which chunk the sorted index falls into
        for cluster_id, group_indices_in_sorted_array in enumerate(split_indices_arrays):
            # Get the original DataFrame indices corresponding to this cluster's chunk
            original_indices_for_cluster = sorted_indices[group_indices_in_sorted_array]
            # Assign the cluster_id to these original indices in the result series
            cluster_assignments.loc[original_indices_for_cluster] = cluster_id

        # Check for any unassigned points (should not happen with array_split but good practice)
        if cluster_assignments.isnull().any():
            unassigned_count = cluster_assignments.isnull().sum()
            self.log_message(f"Warning: {unassigned_count} outlet(s) were not assigned a cluster during angular split. This is unexpected. Assigning them to cluster 0.")
            cluster_assignments.fillna(0, inplace=True) # Assign NaNs to cluster 0 as fallback

        return cluster_assignments.astype(np.int64) # Ensure final type is integer


    def create_optimized_routes_for_clusters(self, num_reps: int) -> Dict[int, List[pd.DataFrame]]:
        """Iterates through clusters, prepares data, and calls VRP solver for each representative."""
        all_cluster_routes: Dict[int, List[pd.DataFrame]] = {} # Store results: {cluster_id: [day1_df, day2_df,...]}
        total_clusters_to_process = max(1, num_reps) # For progress calculation, avoid division by zero
        processed_cluster_count = 0
        progress_start = 30 # Starting progress percentage for this VRP stage
        progress_range = 55 # Total progress percentage allocated to VRP solving

        # --- Pre-checks ---
        if num_reps <= 0:
            self.log_message("Route Generation: Skipping - 0 representatives specified.")
            return {}
        if self.outlets_data is None or 'cluster' not in self.outlets_data.columns:
            err_msg = "Route Generation Error: Missing outlet data or 'cluster' assignments. Cannot generate routes."
            self.queue.put(('error', err_msg))
            self.log_message(f"ERROR: {err_msg}")
            return {}
        if not pd.api.types.is_integer_dtype(self.outlets_data['cluster']):
            err_msg = "Route Generation Error: Cluster column is not of integer type. Cannot proceed."
            self.queue.put(('error', err_msg))
            self.log_message(f"ERROR: {err_msg}")
            return {}

        # --- Process Each Cluster (Representative) ---
        for cluster_id in range(num_reps): # K-Means labels are 0 to num_reps-1
            rep_num = cluster_id + 1
            # Update progress and status for the current representative
            current_progress = progress_start + int(progress_range * (processed_cluster_count / total_clusters_to_process))
            self.queue.put(('progress', current_progress))
            self.queue.put(('status', f"Processing routes for Rep {rep_num}/{num_reps}..."))

            # Get data specific to this cluster
            cluster_mask = (self.outlets_data['cluster'] == cluster_id)
            cluster_data = self.outlets_data[cluster_mask].copy()

            if cluster_data.empty:
                self.log_message(f"--- Rep {rep_num}: Skipping route generation - No outlets assigned to this cluster. ---")
                all_cluster_routes[cluster_id] = [] # Explicitly store empty list for this rep
                processed_cluster_count += 1
                continue # Move to the next representative

            self.log_message(f"\n--- Processing Rep {rep_num} (Cluster ID {cluster_id}) with {len(cluster_data)} outlets ---")

            # --- Data Splitting for Alternating Weeks ---
            vf4_outlets = cluster_data[cluster_data['vf'] == 4]
            vf2_outlets = cluster_data[cluster_data['vf'] == 2]
            self.log_message(f"  Cluster composition: VF4={len(vf4_outlets)}, VF2={len(vf2_outlets)}.")

            # Split VF2 outlets into two groups (A and B)
            # vf2_sorted = vf2_outlets.copy() # No longer needed as sort_values creates a copy by default if not inplace
            # With K-Means, radius splitting might not be as relevant as outlets are already spatially grouped.
            # Change from random shuffling to sorting by latitude.
            vf2_sorted = vf2_outlets.sort_values(by='latitude').reset_index(drop=True)
            split_method = "sorted latitude"
            self.log_message(f"  Splitting VF2 outlets by {split_method}.") # Updated log message


            num_vf2 = len(vf2_sorted)
            split_index = num_vf2 // 2 # Find the midpoint for splitting
            vf2_group_A = vf2_sorted.iloc[:split_index]
            vf2_group_B = vf2_sorted.iloc[split_index:]
            self.log_message(f"  VF2 split ({split_method}): Group A ({len(vf2_group_A)}), Group B ({len(vf2_group_B)}).")

            # Create datasets for the two alternating cycles:
            # Weeks A/C = All VF4 + VF2 Group A
            outlets_AC = pd.concat([vf4_outlets, vf2_group_A], ignore_index=True) if not vf4_outlets.empty or not vf2_group_A.empty else pd.DataFrame()
            # Weeks B/D = All VF4 + VF2 Group B
            outlets_BD = pd.concat([vf4_outlets, vf2_group_B], ignore_index=True) if not vf4_outlets.empty or not vf2_group_B.empty else pd.DataFrame()

            # --- Plan Routes for Each Subset ---
            self.log_message(f"  Planning routes for Weeks A/C subset ({len(outlets_AC)} outlets)...")
            # plan_days_for_outlets returns list of DFs or None on error
            routes_AC = [] if outlets_AC.empty else self.plan_days_for_outlets(outlets_AC, cluster_id, "Weeks A/C", self.params['working_days'])

            self.log_message(f"  Planning routes for Weeks B/D subset ({len(outlets_BD)} outlets)...")
            routes_BD = [] if outlets_BD.empty else self.plan_days_for_outlets(outlets_BD, cluster_id, "Weeks B/D", self.params['working_days'])

            # --- Combine and Store Results ---
            # Only store results if BOTH planning steps succeeded (returned a list, even if empty)
            if routes_AC is not None and routes_BD is not None:
                 combined_routes_for_rep = routes_AC + routes_BD # Concatenate the lists of daily DataFrames
                 if combined_routes_for_rep: # Check if the combined list is not empty
                     all_cluster_routes[cluster_id] = combined_routes_for_rep
                     self.log_message(f"  Successfully planned {len(routes_AC)} day(s) for A/C and {len(routes_BD)} day(s) for B/D for Rep {rep_num}.")
                 else:
                     # Both subsets resulted in empty routes (e.g., no outlets in either)
                     self.log_message(f"  Rep {rep_num}: No routes were generated (both A/C and B/D planning resulted in empty lists).")
                     all_cluster_routes[cluster_id] = [] # Store empty list for this rep
            else:
                # Planning failed for one or both subsets (returned None)
                failed_subsets = []
                if routes_AC is None: failed_subsets.append("A/C")
                if routes_BD is None: failed_subsets.append("B/D")
                error_msg = f"Route planning failed for Rep {rep_num} (subset(s): {', '.join(failed_subsets)}). This representative will have no routes."
                self.log_message(f"ERROR: {error_msg}")
                # Don't send error to queue here, as the VRP function already logged specific errors
                # self.queue.put(('error', error_msg)) # Avoid duplicate error messages
                all_cluster_routes[cluster_id] = [] # Store empty list for failed reps

            processed_cluster_count += 1 # Increment count for progress calculation

        # --- Finalization ---
        self.queue.put(('progress', progress_start + progress_range)) # Mark end of VRP stage progress
        # Count reps for whom we have a list (even if empty), indicates planning didn't critically fail to return None
        successful_reps = len(all_cluster_routes)
        self.log_message(f"\nFinished generating route plans for {successful_reps}/{num_reps} representative(s).")
        return all_cluster_routes

    def plan_days_for_outlets(self, outlets_df: pd.DataFrame, cluster_id: int, week_type: str, working_days: int) -> Optional[List[pd.DataFrame]]:
        """Uses OR-Tools VRP solver to plan daily routes for a given set of outlets."""
        # Prefix for logging messages specific to this planning run
        log_prefix = f"Rep {cluster_id + 1}, {week_type}"
        if outlets_df.empty:
            self.log_message(f"  {log_prefix}: No outlets provided for planning. Returning empty route list.")
            return [] # Success, but no routes needed

        # --- 1. Data Preparation and Validation ---
        required_cols = ['latitude', 'longitude', 'outletname', 'vf']
        if not all(col in outlets_df.columns for col in required_cols):
            missing = set(required_cols) - set(outlets_df.columns)
            self.log_message(f"ERROR ({log_prefix}): Input DataFrame is missing required columns: {missing}. Cannot plan routes.")
            self.queue.put(('error', f"{log_prefix}: Input data missing columns {missing}")) # Notify user
            return None # Indicate critical failure

        # Retrieve VRP parameters
        min_visits_per_day = self.params.get('min_outlets', 1)
        max_visits_per_day = self.params.get('max_outlets', 1)
        if not isinstance(max_visits_per_day, int) or max_visits_per_day <= 0:
            self.log_message(f"ERROR ({log_prefix}): Invalid 'max outlets per day' parameter ({max_visits_per_day}). Must be > 0.")
            self.queue.put(('error', f"{log_prefix}: Invalid Max Outlets parameter ({max_visits_per_day})"))
            return None
        if not isinstance(min_visits_per_day, int) or min_visits_per_day < 0:
             self.log_message(f"Warning ({log_prefix}): Invalid 'min outlets per day' parameter ({min_visits_per_day}). Using 0.")
             min_visits_per_day = 0 # Allow 0 minimum visits

        # Create a clean copy for VRP, drop rows with missing coordinates
        vrp_data = outlets_df[required_cols].copy()
        initial_count = len(vrp_data)
        vrp_data.dropna(subset=['latitude', 'longitude'], inplace=True)
        valid_count = len(vrp_data)
        if initial_count != valid_count:
            self.log_message(f"  {log_prefix}: Dropped {initial_count - valid_count} outlets due to missing coordinates before VRP.")
        if vrp_data.empty:
            self.log_message(f"ERROR ({log_prefix}): No outlets with valid coordinates remain after filtering. Cannot plan routes.")
            self.queue.put(('error', f"{log_prefix}: No outlets with valid coordinates"))
            return None # Indicate failure, no outlets to route

        vrp_data = vrp_data.reset_index(drop=True) # Ensure clean 0-based index for VRP mapping
        n_valid_outlets_for_vrp = len(vrp_data)

        # --- 2. Determine Number of Vehicles (Days) ---
        # Calculate vehicles needed based on max capacity, capped by working days & available outlets
        days_estimated = math.ceil(n_valid_outlets_for_vrp / max_visits_per_day) if max_visits_per_day > 0 else n_valid_outlets_for_vrp
        # Ensure at least 1 vehicle if there are outlets, respect working days limit, respect # outlets
        num_vehicles = max(1, min(days_estimated, working_days, n_valid_outlets_for_vrp)) if n_valid_outlets_for_vrp > 0 else 0

        # Handle case where no vehicles are needed (e.g., no valid outlets left)
        if num_vehicles == 0:
             self.log_message(f"  {log_prefix}: No vehicles (days) required as there are no valid outlets to plan.")
             return [] # Return empty list, not an error

        self.log_message(f"  Planning {log_prefix}: {n_valid_outlets_for_vrp} valid outlets -> Target: {num_vehicles} day(s) (Constraints: Min/Max Visits {min_visits_per_day}/{max_visits_per_day}).")

        # --- 3. Prepare Data for OR-Tools (Locations, Distance Matrix) ---
        # Define depot location (using mean of cluster's outlets)
        try:
            depot_location = vrp_data[['latitude', 'longitude']].mean().values
            # VRP locations array: [depot, outlet1, outlet2, ...]
            vrp_locations = np.vstack([depot_location, vrp_data[['latitude', 'longitude']].values])
            num_vrp_locations = len(vrp_locations) # Includes depot (index 0)
        except Exception as e:
            self.log_message(f"ERROR ({log_prefix}): Failed to calculate depot or stack locations for VRP: {e}")
            self.queue.put(('error', f"{log_prefix}: Failed to prepare VRP locations: {e}"))
            return None

        # Calculate Distance Matrix using the new helper method
        distance_matrix, distance_method_name, max_dist_meters = self._calculate_distance_matrix(vrp_locations, log_prefix)

        if distance_matrix is None: # Check if matrix calculation failed
            self.log_message(f"ERROR ({log_prefix}): Distance matrix calculation failed. Cannot proceed with VRP.")
            # _calculate_distance_matrix should log specific errors and queue user messages
            return None

        if distance_method_name == "Haversine":
            self.log_message(f"Warning ({log_prefix}): Distance calculations are based on the Haversine formula (as-the-crow-flies) and do not represent actual road network travel. Resulting routes may be suboptimal.")

        # --- 4. Initialize OR-Tools Routing Model ---
        try:
            manager = pywrapcp.RoutingIndexManager(num_vrp_locations, num_vehicles, 0) # depot index is 0
            routing = pywrapcp.RoutingModel(manager)
        except Exception as e:
            self.log_message(f"ERROR ({log_prefix}): Failed to initialize OR-Tools RoutingIndexManager or RoutingModel: {e}\n{traceback.format_exc()}")
            self.queue.put(('error', f"{log_prefix}: OR-Tools model init failed: {e}"))
            return None

        # --- 5. Define Callbacks and Constraints ---
        # Distance Callback (returns distance between two VRP indices)
        def distance_callback(from_index, to_index):
            from_node = manager.IndexToNode(from_index)
            to_node = manager.IndexToNode(to_index)
            if 0 <= from_node < num_vrp_locations and 0 <= to_node < num_vrp_locations:
                return distance_matrix[from_node, to_node]
            else: # Should not happen if model is correct
                self.log_message(f"Warning ({log_prefix}): Invalid node index encountered in distance_callback ({from_node}, {to_node})")
                return 999999999 # Return large distance
        try:
            transit_callback_index = routing.RegisterTransitCallback(distance_callback)
            routing.SetArcCostEvaluatorOfAllVehicles(transit_callback_index)
        except Exception as e:
            self.log_message(f"ERROR ({log_prefix}): Failed to register distance callback or set arc cost: {e}")
            self.queue.put(('error', f"{log_prefix}: Failed distance callback setup: {e}"))
            return None

        # Demand Callback (each outlet = 1 unit of capacity)
        # Demands list: [depot_demand, outlet1_demand, ...]
        vrp_demands = [0] + [1] * n_valid_outlets_for_vrp
        def demand_callback(from_index):
            from_node = manager.IndexToNode(from_index)
            if 0 <= from_node < len(vrp_demands):
                return vrp_demands[from_node]
            else: # Should not happen
                self.log_message(f"Warning ({log_prefix}): Invalid node index encountered in demand_callback ({from_node})")
                return 999 # Return large demand
        try:
            demand_callback_index = routing.RegisterUnaryTransitCallback(demand_callback)
            # Add Capacity Dimension Constraint (max outlets per day)
            routing.AddDimensionWithVehicleCapacity(
                name='Capacity', # Correct argument name
                evaluator_index=demand_callback_index,
                slack_max=0,  # No waiting time considered here
                vehicle_capacities=[max_visits_per_day] * num_vehicles, # Max visits per vehicle (day)
                fix_start_cumul_to_zero=True # Start count at 0 for each vehicle
            )
        except Exception as e:
            # Log the specific error, including traceback for details
            self.log_message(f"ERROR ({log_prefix}): Failed to register demand callback or add capacity dimension: {e}\n{traceback.format_exc()}")
            self.queue.put(('error', f"{log_prefix}: Failed capacity constraint setup: {e}"))
            return None

        # Add Soft Lower Bound for Minimum Visits per Day (optional but recommended)
        if min_visits_per_day > 0:
            try:
                # Penalty for routes with fewer visits than minimum.
                # Set a high penalty, e.g., slightly more than max possible route cost if all nodes were visited
                penalty = (max_dist_meters * num_vrp_locations * 2) if max_dist_meters > 0 else 10000000 # Heuristic penalty
                capacity_dimension = routing.GetDimensionOrDie('Capacity')
                for vehicle_id in range(num_vehicles):
                    # Apply soft lower bound to the cumulative variable at the vehicle's end node
                    end_node_index = routing.End(vehicle_id)
                    capacity_dimension.SetCumulVarSoftLowerBound(end_node_index, min_visits_per_day, penalty)
                self.log_message(f"  {log_prefix}: Applied soft lower bound of {min_visits_per_day} visits per day to end nodes.")
            except AttributeError as ae:
                 # Catch if SetCumulVarSoftLowerBound is also missing (unlikely but possible)
                 self.log_message(f"Warning ({log_prefix}): Failed to add minimum visit soft lower bound constraint: {ae}. Your OR-Tools version might not support this method directly on the dimension. Optimization will proceed without it.")
            except Exception as e:
                # Log other errors, but don't necessarily stop the process
                self.log_message(f"Warning ({log_prefix}): Failed to add minimum visit soft lower bound constraint: {e}. Optimization will proceed without it.")
        else:
             self.log_message(f"  {log_prefix}: Minimum visits set to 0, skipping soft lower bound constraint.")

        # --- 6. Set Search Parameters and Solve ---
        search_parameters = pywrapcp.DefaultRoutingSearchParameters()
        # Strategy for finding the first solution
        search_parameters.first_solution_strategy = (
            routing_enums_pb2.FirstSolutionStrategy.AUTOMATIC) # Usually a good starting point

        # Try TABU_SEARCH as the local search metaheuristic
        self.log_message(f"  {log_prefix}: Using TABU_SEARCH for local search.")
        search_parameters.local_search_metaheuristic = (
            routing_enums_pb2.LocalSearchMetaheuristic.TABU_SEARCH) # Changed from GUIDED_LOCAL_SEARCH

        # Time limit for the solver
        solver_time_limit_seconds = self.params.get('time_limit', 30)
        search_parameters.time_limit.FromSeconds(solver_time_limit_seconds)
        # search_parameters.log_search = True # Uncomment for verbose OR-Tools solver logs

        self.queue.put(('status', f"Solving VRP for {log_prefix} ({solver_time_limit_seconds}s limit)..."))
        solution = routing.SolveWithParameters(search_parameters)
        solver_status_code = routing.status() # Get the status code after solving

        # --- 7. Process the Solution ---
        # Helper to convert status code to readable string
        def get_solver_status_string(status_code):
            # Use the instance's STATUS_MAP initialized earlier
            return self.STATUS_MAP.get(status_code, f"UNKNOWN_STATUS_{status_code}")

        status_name = get_solver_status_string(solver_status_code)

        if solution:
            # Use the integer codes stored during initialization
            is_solution_usable = (solver_status_code == self.ROUTING_SUCCESS_CODE or
                                  solver_status_code == self.ROUTING_FAIL_TIMEOUT_CODE)

            if not is_solution_usable:
                 self.log_message(f"ERROR ({log_prefix}): Solver finished but status indicates failure or no solution found ({status_name} - Code: {solver_status_code}). Cannot extract routes.")
                 self.queue.put(('error', f"Optimizer ({log_prefix}) failed to find a usable solution (Status: {status_name})"))
                 return None # Indicate failure

            self.log_message(f"  {log_prefix}: Solution found by solver (Status: {status_name} - Code: {solver_status_code})")
            if solver_status_code != self.ROUTING_SUCCESS_CODE: # Use the stored integer code
                warning_msg = f"Solver for {log_prefix} finished with status {status_name}. Solution might be suboptimal or incomplete due to time limit or other issues."
                self.log_message(f"    WARNING: {warning_msg}")
                self.queue.put(('warning', warning_msg))

            # --- Extract Routes from Solution ---
            daily_routes_list_of_dfs: List[pd.DataFrame] = []
            total_distance_meters = 0
            total_visits_assigned = 0
            assigned_vrp_data_indices = set() # Track original indices from vrp_data that are assigned

            for vehicle_id in range(num_vehicles):
                index = routing.Start(vehicle_id)
                route_vrp_data_indices = [] # Store original indices from vrp_data for this route
                route_distance_meters = 0
                # route_node_sequence = [] # Optional: for debugging VRP nodes

                while not routing.IsEnd(index):
                    node_index = manager.IndexToNode(index)
                    # route_node_sequence.append(node_index)
                    if node_index != 0: # If it's not the depot (node 0)
                        vrp_data_index = node_index - 1 # Map VRP node index (1..N) to vrp_data index (0..N-1)
                        if 0 <= vrp_data_index < n_valid_outlets_for_vrp:
                            route_vrp_data_indices.append(vrp_data_index)
                            assigned_vrp_data_indices.add(vrp_data_index)
                        else: # Should not happen if logic is correct
                             self.log_message(f"Warning ({log_prefix}, Day {vehicle_id+1}): Invalid VRP data index {vrp_data_index} derived from node {node_index}.")

                    previous_index = index
                    index = solution.Value(routing.NextVar(index))
                    # Accumulate distance using the model's cost function
                    route_distance_meters += routing.GetArcCostForVehicle(previous_index, index, vehicle_id)

                # route_node_sequence.append(manager.IndexToNode(routing.End(vehicle_id))) # Add end node index

                # If the route visited any outlets (not just depot back to depot)
                if route_vrp_data_indices:
                    # Create DataFrame for this day's route using the collected original indices
                    day_df = vrp_data.iloc[route_vrp_data_indices].copy()
                    # Add visit order based on the sequence found by the solver
                    # Create a mapping from original index back to its position in the route list
                    original_index_to_order = {orig_idx: order + 1 for order, orig_idx in enumerate(route_vrp_data_indices)}
                    day_df['Visit Order'] = day_df.index.map(original_index_to_order)

                    daily_routes_list_of_dfs.append(day_df)
                    total_distance_meters += route_distance_meters
                    total_visits_assigned += len(day_df)

                    # Optional: Log details of the generated route for this day
                    # self.log_message(f"    Day {vehicle_id + 1}: {len(day_df)} visits, Dist: {(route_distance_meters / 1000.0):.1f}km. Nodes: {route_node_sequence}")

            # --- Log Summary and Check Unassigned ---
            num_days_with_routes = len(daily_routes_list_of_dfs)
            avg_daily_dist_km = (total_distance_meters / 1000.0) / num_days_with_routes if num_days_with_routes > 0 else 0
            self.log_message(f"  {log_prefix} Solution Summary: Assigned {total_visits_assigned}/{n_valid_outlets_for_vrp} outlets across {num_days_with_routes} active day(s).")
            if num_days_with_routes > 0:
                self.log_message(f"    Total Route Distance: {(total_distance_meters / 1000.0):.1f} km.")
                self.log_message(f"    Average Daily Distance: {avg_daily_dist_km:.1f} km.")

            # Check for outlets that were not assigned to any route
            unassigned_indices = set(range(n_valid_outlets_for_vrp)) - assigned_vrp_data_indices
            if unassigned_indices:
                unassigned_names = vrp_data.iloc[list(unassigned_indices)]['outletname'].tolist()
                warning_unassigned = f"{log_prefix}: {len(unassigned_indices)} outlets could not be assigned to routes by the solver."
                self.log_message(f"    WARNING: {warning_unassigned}")
                self.log_message(f"      Unassigned Outlets: {unassigned_names[:5]}..." if len(unassigned_names) > 5 else unassigned_names)
                self.queue.put(('warning', warning_unassigned))

            return daily_routes_list_of_dfs # Return the list of DataFrames (one per day)

        else: # No solution object was returned by .SolveWithParameters()
            self.log_message(f"ERROR ({log_prefix}): No solution object was returned by the solver. Solver status: {status_name}")
            self.queue.put(('error', f"Optimizer ({log_prefix}) failed: No solution returned (Status: {status_name})"))
            return None # Indicate critical failure

    def create_schedule(self):
        """Constructs the 4-week alternating schedule based on the generated routes stored in self.routes."""
        self.log_message("\n--- Creating 4-Week Schedule ---")
        self.schedule = {} # Reset schedule dictionary for this run

        # Check if self.routes is a dictionary and not empty
        if not isinstance(self.routes, dict) or not self.routes:
            self.log_message("Schedule Creation: No routes available (self.routes is empty or not a dict). Cannot create schedule.")
            return # Nothing to schedule

        # Check for potentially missing cluster info (less critical here, affects split logic)
        if self.outlets_data is None or 'cluster' not in self.outlets_data.columns:
            self.log_message("Schedule Creation Warning: Outlet data or cluster information missing. Split between A/C and B/D weeks might use default halfway split.")

        # Get working days from validated parameters, with fallback
        working_days_param = self.params.get('working_days', 5)
        if not (isinstance(working_days_param, int) and 0 < working_days_param <= 7):
            self.log_message(f"Schedule Creation Warning: Invalid 'working_days' parameter found ({working_days_param}). Using default value of 5.")
            wd = 5
        else:
            wd = working_days_param

        days_of_week_names = list(calendar.day_name)[:wd] # Get names like ['Monday', 'Tuesday', ...]

        # Iterate through each representative's routes
        # Ensure we iterate through items of the dictionary
        for rep_id, combined_routes_for_rep in self.routes.items():
            rep_name = f'Rep {rep_id + 1}'

            # Validate the structure of routes for this rep
            if not isinstance(combined_routes_for_rep, list):
                self.log_message(f"Schedule Warning (Rep {rep_name}): Invalid route data found (expected list of DataFrames, got {type(combined_routes_for_rep)}). Skipping schedule for this rep.")
                continue

            if not combined_routes_for_rep:
                self.log_message(f"Schedule Info (Rep {rep_name}): No routes were generated or assigned for this rep in the VRP stage. Skipping schedule creation.")
                continue # Skip reps with no routes planned

            # --- Determine Split Point between A/C and B/D Routes ---
            # This logic assumes routes_AC were added first, then routes_BD in create_optimized_routes_for_clusters
            split_point_index = 0
            try:
                # Attempt to estimate split based on original outlet counts for the cluster
                cluster_data = self.outlets_data[self.outlets_data['cluster'] == rep_id] if self.outlets_data is not None and 'cluster' in self.outlets_data else pd.DataFrame()

                if not cluster_data.empty:
                    vf4_count = (cluster_data['vf'] == 4).sum()
                    vf2_count = (cluster_data['vf'] == 2).sum()
                    vf2_group_A_count = vf2_count // 2 # Matches split logic
                    outlets_in_AC_subset = vf4_count + vf2_group_A_count
                    max_visits_param = max(1, self.params.get('max_outlets', 1)) # Ensure > 0 divisor

                    # Estimate days needed for A/C subset based on max capacity
                    estimated_days_for_AC = math.ceil(outlets_in_AC_subset / max_visits_param) if outlets_in_AC_subset > 0 else 0

                    # Determine split point: cap estimated days by working days and total routes found
                    split_point_index = min(max(0, estimated_days_for_AC), wd, len(combined_routes_for_rep))
                    self.log_message(f"  Sched Split ({rep_name}): Estimated {estimated_days_for_AC} A/C days based on VF counts -> Split point at index {split_point_index}.")
                else:
                    # Fallback: If cluster data missing, split roughly in half
                    split_point_index = math.ceil(len(combined_routes_for_rep) / 2.0)
                    self.log_message(f"  Sched Split ({rep_name}): Cluster data missing or unavailable, fallback split roughly in half -> Split point at index {int(split_point_index)}.")

            except Exception as e:
                # Fallback on any error during estimation (e.g., parameter missing)
                split_point_index = math.ceil(len(combined_routes_for_rep) / 2.0)
                self.log_message(f"  Sched Split Error ({rep_name}): Could not estimate split point due to error ({e}). Fallback split roughly in half -> Split point at index {int(split_point_index)}.")

            # Ensure split_point is an integer index
            split_point_index = int(split_point_index)

            # Perform the actual split based on calculated index
            actual_routes_AC = combined_routes_for_rep[:split_point_index]
            actual_routes_BD = combined_routes_for_rep[split_point_index:]
            self.log_message(f"  Sched Split ({rep_name}): Actual split resulted in {len(actual_routes_AC)} A/C day(s), {len(actual_routes_BD)} B/D day(s).")

            # Pad route lists with empty DataFrames to match number of working days for easier looping
            padded_routes_AC = actual_routes_AC + [pd.DataFrame()] * max(0, wd - len(actual_routes_AC))
            padded_routes_BD = actual_routes_BD + [pd.DataFrame()] * max(0, wd - len(actual_routes_BD))

            # --- Generate Schedule Entries for 4 Weeks ---
            rep_schedule_entries_list = []
            for week_number in range(1, 5): # Iterate through weeks 1, 2, 3, 4
                 # Determine if it's an A/C week (odd) or B/D week (even)
                 is_AC_type_week = (week_number % 2 != 0)
                 routes_for_this_week = padded_routes_AC if is_AC_type_week else padded_routes_BD
                 week_type_label = "A/C" if is_AC_type_week else "B/D"

                 # Iterate through the working days of the week
                 for day_index, day_name in enumerate(days_of_week_names):
                     # Get the corresponding route DataFrame for this day (could be empty DF if padded)
                     daily_route_df = routes_for_this_week[day_index] if day_index < len(routes_for_this_week) else pd.DataFrame()

                     outlet_name_list = []
                     visit_count = 0

                     # Process the DataFrame if it's valid and not empty
                     if isinstance(daily_route_df, pd.DataFrame) and not daily_route_df.empty:
                         if 'outletname' in daily_route_df.columns:
                             # Sort by Visit Order if available, otherwise use DataFrame order
                             df_to_process = daily_route_df.copy()
                             if 'Visit Order' in df_to_process.columns and pd.api.types.is_numeric_dtype(df_to_process['Visit Order']):
                                  # Ensure 'Visit Order' is numeric for sorting, handle errors gracefully
                                  df_to_process['Visit Order'] = pd.to_numeric(df_to_process['Visit Order'], errors='coerce').fillna(9999)
                                  df_to_process = df_to_process.sort_values('Visit Order')
                             else:
                                 self.log_message(f"Schedule Warning ({rep_name} W{week_number} {day_name}): 'Visit Order' column missing or not numeric. Using existing row order for outlet list.")
                                 # If no visit order, still use the df as is
                             # Extract outlet names
                             outlet_name_list = df_to_process['outletname'].astype(str).tolist()
                             visit_count = len(df_to_process)
                         else:
                             # Handle case where route DF exists but 'outletname' is missing
                             outlet_name_list = ["Error: Outlet Name Column Missing"] * len(daily_route_df)
                             visit_count = len(daily_route_df)
                             self.log_message(f"Schedule Error ({rep_name} W{week_number} {day_name}): Route DataFrame found but 'outletname' column is missing.")
                     # else: Day has no route (empty DataFrame from padding or no route generated)
                     # outlet_name_list remains [], visit_count remains 0

                     # Create dictionary entry for this day
                     rep_schedule_entries_list.append({
                         'Week': week_number,
                         'Day': day_name,
                         'Week Type': week_type_label,
                         'Outlets': outlet_name_list, # List of outlet names in visit order
                         'Count': visit_count,        # Number of visits for the day
                         'RouteDF': daily_route_df    # Store the original DataFrame for potential later use (e.g., maps)
                     })

            # Add the generated list of daily entries to the main schedule dictionary for this rep
            if rep_schedule_entries_list:
                self.schedule[rep_name] = rep_schedule_entries_list

        # --- Final Log Message ---
        if not self.schedule or not any(self.schedule.values()): # Check if schedule is empty or contains only empty lists
            self.log_message("Schedule Creation Finished: No schedules were generated (possibly due to no routes or errors during scheduling).")
        else:
            reps_in_schedule = len([rep for rep, entries in self.schedule.items() if entries]) # Count reps with actual schedule entries
            self.log_message(f"Schedule Creation Finished: Schedules generated for {reps_in_schedule} representative(s).")


    def start_export(self):
        """Initiates the export process (Excel, Maps) in a background thread."""
        if self.processing:
            self.log_message("Export request ignored: Another process is currently running.")
            messagebox.showwarning("Busy", "Optimization or Export is already in progress. Please wait.", parent=self.root)
            return

        # --- Check if there is data to export ---
        # Needs self.schedule to be a dict, non-empty, and contain at least one day with a non-empty RouteDF
        has_data_to_export = False
        if isinstance(self.schedule, dict) and self.schedule:
             try: # Add try-except for robustness during check
                 has_data_to_export = any(
                     isinstance(entries, list) and entries and # Rep has a list of entries
                     any(isinstance(day_info, dict) and # Entry is a dict
                         isinstance(day_info.get('RouteDF'), pd.DataFrame) and # RouteDF is a DataFrame
                         not day_info['RouteDF'].empty # And it's not empty
                         for day_info in entries) # Check each day's entry
                     for entries in self.schedule.values() # Check each rep's list
                 )
             except Exception as e_check:
                  self.log_message(f"Error checking schedule data for export: {e_check}")
                  has_data_to_export = False # Assume no data on error

        if not has_data_to_export:
            self.log_message("Export: No schedule data containing routes found to export.")
            messagebox.showinfo("Export Info", "There is no schedule data with planned routes available to export. Please run the optimization first.", parent=self.root)
            return

        # --- Proceed with export ---
        self.processing = True
        self.disable_buttons() # Disable UI
        self.log_message("\n" + "="*15 + " Starting Results Export " + "="*15)
        self.progress_var.set(0)
        self.status_var.set("Initializing export...")

        # Start export task in a separate thread
        threading.Thread(target=self.export_results_task, daemon=True).start()


    def export_results_task(self):
        """Worker thread function for exporting schedule to Excel and maps to HTML."""
        base_export_dir = "" # Will be set later
        excel_subdir = ""
        maps_subdir = ""
        export_succeeded = False # Flag to track overall success for final message

        try:
            self.queue.put(('status', "Preparing export directories..."))
            self.queue.put(('progress', 5))

            # --- Re-check data existence within the thread (belt and suspenders) ---
            has_data = False
            if isinstance(self.schedule, dict) and self.schedule:
                 try:
                     has_data = any(
                         isinstance(entries, list) and entries and
                         any(isinstance(day_info, dict) and isinstance(day_info.get('RouteDF'), pd.DataFrame) and not day_info['RouteDF'].empty
                             for day_info in entries)
                         for entries in self.schedule.values()
                     )
                 except Exception: has_data = False # Assume no data on error during check
            if not has_data:
                self.log_message("Export Task Error: No valid schedule data with routes found within the export thread.")
                self.queue.put(('error', "Export Failed: No schedule data with routes available."))
                # Must signal completion even on early exit
                self.queue.put(('complete', 'export'))
                return # Exit export thread

            # --- Create Export Directories ---
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            # Use user's home directory or a fallback like current working directory
            try:
                # Try to get the user's home directory
                home_dir = os.path.expanduser("~")
            except Exception:
                # Fallback to current working directory if home dir is not accessible
                home_dir = os.getcwd()
                self.log_message(f"Warning: Could not access user home directory. Using current directory: {home_dir}")

            # Create base directory inside home or CWD
            base_export_dir = os.path.join(home_dir, f"Route_Optimizer_Results_{timestamp}")

            excel_subdir = os.path.join(base_export_dir, "Rep_Schedules_Excel")
            maps_subdir = os.path.join(base_export_dir, "Route_Maps_HTML")
            self.last_export_dir = base_export_dir # Store for potential "Open Folder" action

            try:
                os.makedirs(excel_subdir, exist_ok=True) # Create parent and subdirs
                os.makedirs(maps_subdir, exist_ok=True)
                self.log_message(f"Created export directory structure: {os.path.abspath(base_export_dir)}")
            except OSError as e:
                self.log_message(f"CRITICAL ERROR: Failed to create export directories at '{base_export_dir}': {e}")
                self.queue.put(('error', f"Directory Creation Failed: {e}. Check permissions."))
                # Must signal completion even on early exit
                self.queue.put(('complete', 'export'))
                return # Exit export thread

            # --- Export Excel Files ---
            self.queue.put(('status', "Exporting schedules to Excel files..."))
            excel_progress_start = 10
            excel_progress_range = 40 # Allocate 40% progress to Excel export

            all_schedule_rows_for_combined_file = [] # Accumulate data for the combined sheet
            exported_rep_files_count = 0

            # Filter schedule data again to only include reps with actual data to export
            reps_with_data_to_export = {
                rep_name: entries for rep_name, entries in self.schedule.items()
                if isinstance(entries, list) and entries and any(
                    isinstance(d, dict) and isinstance(d.get('RouteDF'), pd.DataFrame) and not d['RouteDF'].empty
                    for d in entries
                )
            }
            total_reps_to_export = max(1, len(reps_with_data_to_export)) # Avoid division by zero

            # Define day order for consistent sorting within Excel files
            day_order_map = {name: i for i, name in enumerate(calendar.day_name)}

            for rep_name, schedule_list_for_rep in reps_with_data_to_export.items():
                current_progress = excel_progress_start + int(excel_progress_range * (exported_rep_files_count / total_reps_to_export))
                self.queue.put(('progress', current_progress))
                self.queue.put(('status', f"Exporting Excel: {rep_name} ({exported_rep_files_count+1}/{total_reps_to_export})..."))

                individual_rep_rows = []
                # Sort the schedule list chronologically (Week, Day) before processing rows
                try:
                    sorted_schedule_list = sorted(
                        schedule_list_for_rep,
                        # Sort key: tuple of (Week number, Day of week index)
                        key=lambda entry: (entry.get('Week', 0), day_order_map.get(entry.get('Day', ''), 99))
                    )
                except Exception as sort_err:
                    self.log_message(f"Warning: Could not sort schedule entries for {rep_name}: {sort_err}. Using original order.")
                    sorted_schedule_list = schedule_list_for_rep # Fallback

                # Iterate through sorted days for this representative
                for entry in sorted_schedule_list:
                    week_num = entry.get('Week', 'N/A')
                    day_name = entry.get('Day', 'N/A')
                    route_df = entry.get('RouteDF')

                    # Process only if RouteDF is a non-empty DataFrame
                    if isinstance(route_df, pd.DataFrame) and not route_df.empty:
                        # Prepare DataFrame rows for export
                        df_for_export = route_df.copy()
                        # Ensure 'Visit Order' exists and is numeric, then sort
                        if 'Visit Order' in df_for_export.columns and pd.api.types.is_numeric_dtype(df_for_export['Visit Order']):
                             df_for_export['Visit Order'] = pd.to_numeric(df_for_export['Visit Order'], errors='coerce').fillna(9999)
                             df_for_export = df_for_export.sort_values(by='Visit Order')
                        else:
                             # If missing or non-numeric, assign sequential order based on current DF order
                             df_for_export['Visit Order'] = range(1, len(df_for_export) + 1)
                             df_for_export = df_for_export.sort_values(by='Visit Order') # Sort by the newly assigned order

                        # Extract row data into dictionaries
                        for _, outlet_row in df_for_export.iterrows():
                            # Ensure Visit_Order is int, handle potential errors
                            try: visit_order_int = int(outlet_row.get('Visit Order', 0))
                            except (ValueError, TypeError): visit_order_int = 0

                            row_dict = {
                                'Representative': rep_name,
                                'Week': week_num,
                                'Day': day_name,
                                'Visit_Order': visit_order_int, # Use cleaned int
                                'Outlet_Name': outlet_row.get('outletname', 'N/A'),
                                'Latitude': outlet_row.get('latitude', np.nan),
                                'Longitude': outlet_row.get('longitude', np.nan),
                                'VF': outlet_row.get('vf', 'N/A')
                            }
                            individual_rep_rows.append(row_dict)
                            all_schedule_rows_for_combined_file.append(row_dict) # Add to combined list as well

                # Write individual Excel file for this representative if rows were generated
                if individual_rep_rows:
                    df_rep_schedule = pd.DataFrame(individual_rep_rows)
                    # Sanitize representative name for use in filename
                    safe_rep_filename = "".join(c if c.isalnum() or c in (' ', '-') else "_" for c in rep_name).replace(" ", "_").replace("__", "_")
                    excel_filepath = os.path.join(excel_subdir, f"{safe_rep_filename}_schedule.xlsx")
                    try:
                        with pd.ExcelWriter(excel_filepath, engine='xlsxwriter') as writer:
                            df_rep_schedule.to_excel(writer, index=False, sheet_name='Schedule')
                            # Auto-adjust column widths for readability
                            worksheet = writer.sheets['Schedule']
                            for i, col in enumerate(df_rep_schedule.columns):
                                series = df_rep_schedule[col]
                                # Calculate max length needed for column (header or data)
                                try: # Add try-except for complex types
                                    max_len_data = series.astype(str).map(len).max() if not series.empty else 0
                                except TypeError: # Handle potential errors with mixed types
                                    max_len_data = series.apply(lambda x: len(str(x))).max() if not series.empty else 0

                                max_len_header = len(str(series.name)) # Len of header
                                max_len = max(max_len_data, max_len_header) + 2 # Add padding

                                worksheet.set_column(i, i, min(max_len, 60)) # Apply width, capped at 60
                        # Optional: Log success per file
                        # self.log_message(f"  Exported schedule for {rep_name} to {os.path.basename(excel_filepath)}")
                    except Exception as e:
                        # Log error for specific file, but continue exporting others
                        self.log_message(f"ERROR writing Excel file for {rep_name} to '{excel_filepath}': {e}")
                        self.queue.put(('error', f"Excel Export Failed for {rep_name}: {e}"))
                exported_rep_files_count += 1

            self.queue.put(('progress', excel_progress_start + excel_progress_range)) # Update progress to 50%

            # --- Export Combined Excel File ---
            if all_schedule_rows_for_combined_file:
                self.queue.put(('status', "Exporting combined schedule file..."))
                df_combined = pd.DataFrame(all_schedule_rows_for_combined_file)

                # Sort combined data comprehensively
                df_combined['DayOrder'] = df_combined['Day'].map(day_order_map).fillna(99) # Add temp column for day sorting
                df_combined = df_combined.sort_values(
                    ['Representative', 'Week', 'DayOrder', 'Visit_Order'] # Use standardized Visit_Order name
                ).drop(columns=['DayOrder']) # Remove temporary sort column

                combined_filepath = os.path.join(base_export_dir, "Combined_Schedule_All_Reps.xlsx")
                try:
                    with pd.ExcelWriter(combined_filepath, engine='xlsxwriter') as writer:
                        df_combined.to_excel(writer, index=False, sheet_name='Combined Schedule')
                        # Auto-adjust column widths for combined sheet
                        worksheet = writer.sheets['Combined Schedule']
                        for i, col in enumerate(df_combined.columns):
                             series = df_combined[col]
                             try: # Add try-except for complex types
                                max_len_data = series.astype(str).map(len).max() if not series.empty else 0
                             except TypeError:
                                max_len_data = series.apply(lambda x: len(str(x))).max() if not series.empty else 0

                             max_len_header = len(str(series.name))
                             max_len = max(max_len_data, max_len_header) + 2
                             worksheet.set_column(i, i, min(max_len, 60))
                    self.log_message(f"Successfully exported combined schedule for all reps to: {os.path.basename(combined_filepath)}")
                except Exception as e:
                    # Log error for combined file
                    self.log_message(f"ERROR writing combined Excel file '{combined_filepath}': {e}")
                    self.queue.put(('error', f"Combined Excel Export Failed: {e}"))
            else:
                self.log_message("Warning: No data rows were generated for any representative. Skipping combined schedule Excel file.")

            # --- Create and Save Route Maps ---
            map_progress_start = 50 # Start map progress at 50%
            map_progress_range = 50 # Allocate 50% to map generation
            self.queue.put(('progress', map_progress_start))
            self.queue.put(('status', "Creating route maps (HTML)..."))
            # Pass the filtered dict of reps with data to the map function
            self.create_and_save_maps(maps_subdir, reps_with_data_to_export, map_progress_start, map_progress_range)

            self.log_message("="*15 + " Export Process Complete " + "="*15)
            export_succeeded = True # Mark export as successful if it reached this point without critical errors

        except Exception as e:
            # Catch any unexpected error during the entire export task
            error_msg = f"CRITICAL EXPORT TASK ERROR: {type(e).__name__}: {e}\n{traceback.format_exc()}"
            self.log_message(error_msg)
            self.queue.put(('error', f"Export Failed Unexpectedly: {e}. Check log."))
            self.queue.put(('status', "Export failed critically. Check log."))
            export_succeeded = False

        finally:
            # This block always runs, ensures progress bar completion and final status update
            self.queue.put(('progress', 100)) # Ensure progress bar reaches 100%

            if export_succeeded and base_export_dir and os.path.exists(base_export_dir):
                # If successful and directory exists, report success and offer to open
                abs_path = os.path.abspath(base_export_dir)
                self.log_message(f"Export process finished. Results saved to folder: {abs_path}")
                self.queue.put(('status', "Export complete. Results saved."))
                self.queue.put(('ask_open_folder', abs_path)) # Ask user via queue handler
            elif export_succeeded:
                # If successful but directory somehow missing (unlikely)
                self.log_message("Export process finished, but the base export directory was not found or is inaccessible.")
                self.queue.put(('status', "Export finished (Output folder issue)."))
            else:
                # If export failed (status was already set in the except block)
                 self.log_message("Export process finished with errors.")
                 # Status should already indicate failure

            # Signal that the export task is complete, regardless of outcome
            self.queue.put(('complete', 'export'))

    def create_and_save_maps(self, maps_dir: str, schedule_data_for_maps: Dict[str, list], progress_start: int, progress_range: int):
        """Creates and saves Folium HTML maps for each representative (showing Week 1 & 2 routes)."""
        self.log_message("\n--- Creating Route Maps ---")
        if not schedule_data_for_maps: # Check the filtered data passed in
            self.log_message("Map Creation: No representative data with routes provided. Skipping map generation.")
            self.queue.put(('progress', progress_start + progress_range)) # Complete progress for this step
            return

        # Define a list of distinct colors for routes (cycled through)
        # Using ColorBrewer Paired colors: https://colorbrewer2.org/#type=qualitative&scheme=Paired&n=12
        route_colors = ['#a6cee3','#1f78b4','#b2df8a','#33a02c','#fb9a99','#e31a1c','#fdbf6f','#ff7f00','#cab2d6','#6a3d9a','#ffff99','#b15928'] * 3 # Repeat colors if more than 12 days

        map_creation_count = 0
        total_reps_for_maps = max(1, len(schedule_data_for_maps)) # Avoid division by zero
        first_map_filepath = None # Store path of the first generated map to offer opening it

        # Iterate through the representatives who have data
        for rep_name, schedule_list in schedule_data_for_maps.items():
            self.log_message(f"  Processing map for {rep_name}...") # Log start of map processing for rep
            # Update progress and status
            current_progress = progress_start + int(progress_range * (map_creation_count / total_reps_for_maps))
            self.queue.put(('progress', current_progress))
            self.queue.put(('status', f"Creating map: {rep_name} ({map_creation_count+1}/{total_reps_for_maps})..."))

            # Sanitize rep name for filename
            safe_rep_filename = "".join(c if c.isalnum() or c in (' ', '-') else "_" for c in rep_name).replace(" ", "_").replace("__", "_")
            map_filepath = os.path.join(maps_dir, f'{safe_rep_filename}_Week1_Week2_Routes.html')

            # Extract route DataFrames specifically for Week 1 (A/C) and Week 2 (B/D)
            routes_week1 = []
            routes_week2 = []
            if isinstance(schedule_list, list): # Ensure schedule_list is actually a list
                routes_week1 = [
                    entry['RouteDF'] for entry in schedule_list
                    if isinstance(entry, dict) and entry.get('Week') == 1 and isinstance(entry.get('RouteDF'), pd.DataFrame) and not entry['RouteDF'].empty
                ]
                routes_week2 = [
                    entry['RouteDF'] for entry in schedule_list
                    if isinstance(entry, dict) and entry.get('Week') == 2 and isinstance(entry.get('RouteDF'), pd.DataFrame) and not entry['RouteDF'].empty
                ]
            else:
                 self.log_message(f"Warning (Map {rep_name}): Expected list for schedule entries, but got {type(schedule_list)}. Skipping map.")
                 map_creation_count += 1
                 continue


            self.log_message(f"    Found {len(routes_week1)} routes for Week 1 and {len(routes_week2)} routes for Week 2.")

            # Skip if no route data found for these specific weeks
            if not routes_week1 and not routes_week2:
                self.log_message(f"  Skipping map for {rep_name}: No valid route data found for Week 1 or Week 2 in the schedule.")
                map_creation_count += 1
                continue

            # --- Determine Map Center and Bounds ---
            all_valid_points_list = []
            # Collect valid lat/lon points from all routes in Week 1 and 2
            for week_num, week_routes in enumerate([routes_week1, routes_week2], 1):
                self.log_message(f"    Checking coordinates for Week {week_num} routes...")
                for day_idx, df in enumerate(week_routes):
                    # Basic check if df is DataFrame and has columns
                    if isinstance(df, pd.DataFrame) and not df.empty and all(c in df for c in ['latitude', 'longitude']):
                        # Log DataFrame info for debugging
                        # self.log_message(f"      Week {week_num}, Day {day_idx+1} DataFrame Info:")
                        # self.log_message(f"        Columns: {df.columns.tolist()}")
                        # self.log_message(f"        DTypes:\n{df.dtypes}")
                        # self.log_message(f"        Head:\n{df.head().to_string()}")

                        points = df[['latitude', 'longitude']].copy()
                        # Convert to numeric, coercing errors, then drop rows with NaN in either coord
                        points['latitude'] = pd.to_numeric(points['latitude'], errors='coerce')
                        points['longitude'] = pd.to_numeric(points['longitude'], errors='coerce')
                        orig_len = len(points)
                        points.dropna(subset=['latitude', 'longitude'], inplace=True)
                        if len(points) != orig_len:
                             self.log_message(f"      Warning: Dropped {orig_len - len(points)} rows with invalid coordinates for W{week_num} D{day_idx+1}.")
                        if not points.empty:
                            all_valid_points_list.append(points)
                            # self.log_message(f"      Added {len(points)} valid points from W{week_num} D{day_idx+1}.")
                        else:
                            self.log_message(f"      Warning: No valid coordinates found in W{week_num} D{day_idx+1} DataFrame.")
                    else:
                         self.log_message(f"      Warning: Invalid or empty DataFrame skipped for W{week_num} D{day_idx+1}.")

            map_center = None
            map_bounds = None
            # Calculate center/bounds if valid points were found
            if all_valid_points_list:
                combined_points_df = pd.concat(all_valid_points_list, ignore_index=True)
                if not combined_points_df.empty:
                    self.log_message(f"    Total valid points for centering/bounds: {len(combined_points_df)}")
                    # Calculate center as the mean lat/lon
                    map_center = combined_points_df.mean().tolist()
                    # Calculate bounding box
                    min_lat, max_lat = combined_points_df['latitude'].min(), combined_points_df['latitude'].max()
                    min_lon, max_lon = combined_points_df['longitude'].min(), combined_points_df['longitude'].max()
                    map_bounds = [[min_lat, min_lon], [max_lat, max_lon]]
                    self.log_message(f"    Calculated map center: {map_center}, bounds: {map_bounds}")
                    # Add padding if the points are very close (prevents excessive zoom)
                    lat_range = max_lat - min_lat
                    lon_range = max_lon - min_lon
                    padding = 0.005 # Small degree padding
                    if lat_range < 0.01: map_bounds[0][0] -= padding; map_bounds[1][0] += padding
                    if lon_range < 0.01: map_bounds[0][1] -= padding; map_bounds[1][1] += padding
                    if lat_range < 0.01 or lon_range < 0.01:
                         self.log_message(f"    Applied padding to map bounds: {map_bounds}")
                else:
                     self.log_message("    Warning: Could not combine points for centering (result was empty).")
            else:
                 self.log_message("    Warning: No valid points collected from Week 1/2 routes for centering.")


            # Fallback Centering Logic (if no points found in W1/W2 routes)
            if map_center is None:
                 self.log_message(f"Warning: Could not determine map center from Week 1/2 routes for {rep_name}. Attempting fallback using cluster data centroid.")
                 try:
                     # Extract rep ID number (e.g., "Rep 1" -> cluster_id 0)
                     cluster_id_for_fallback = int(rep_name.split(' ')[-1]) - 1 # Avoid reusing cluster_id from outer scope
                     if self.outlets_data is not None and 'cluster' in self.outlets_data.columns:
                          cluster_data_fallback = self.outlets_data[
                              (self.outlets_data['cluster'] == cluster_id_for_fallback) &
                              self.outlets_data['latitude'].notna() &
                              self.outlets_data['longitude'].notna()
                          ].copy()
                          if not cluster_data_fallback.empty:
                              # Ensure coords are numeric for mean calculation
                              cluster_data_fallback['latitude'] = pd.to_numeric(cluster_data_fallback['latitude'], errors='coerce')
                              cluster_data_fallback['longitude'] = pd.to_numeric(cluster_data_fallback['longitude'], errors='coerce')
                              cluster_data_fallback.dropna(subset=['latitude', 'longitude'], inplace=True)
                              if not cluster_data_fallback.empty:
                                   map_center = cluster_data_fallback[['latitude', 'longitude']].mean().tolist()
                                   self.log_message(f"  Fallback center for {rep_name} set from cluster {cluster_id_for_fallback} data centroid: {map_center}")
                          if map_center is None: # If cluster data existed but had no valid coords
                              self.log_message(f"Warning: Fallback centering failed - No valid outlets with coordinates found for cluster {cluster_id_for_fallback}.")
                     else:
                         self.log_message("Warning: Fallback centering failed - Outlet data or cluster column missing.")
                 except (ValueError, IndexError, TypeError, KeyError) as fallback_err:
                      self.log_message(f"Warning: Error during fallback centering calculation for {rep_name}: {fallback_err}")

            # Absolute Fallback Centering (if all else fails)
            if map_center is None:
                 map_center = [24.7136, 46.6753] # Default coordinates (e.g., Riyadh)
                 map_bounds = None # Cannot determine bounds
                 self.log_message(f"Warning: Map for {rep_name} using default center coordinates ({map_center}). Map bounds not set.")

            # --- Create Folium Map Object ---
            try:
                # Use a cleaner default tile layer like CartoDB positron
                folium_map = folium.Map(location=map_center, zoom_start=11, tiles='CartoDB positron')
                self.log_message(f"    Folium map object created for {rep_name}.")
            except Exception as e:
                self.log_message(f"ERROR creating Folium map object for {rep_name}: {e}")
                map_creation_count += 1 # Increment count even on failure here
                continue # Skip to next rep

            # --- Nested Function to Add Routes/Markers for a Specific Week ---
            def add_week_routes_to_map(week_number, routes_list_for_week, week_type_label, color_start_offset=0):
                """Adds markers and polylines for a given week's routes to the map."""
                if not routes_list_for_week: return # Skip if no routes for this week

                # Create Folium FeatureGroups for layer control
                fg_route_lines = folium.FeatureGroup(name=f"Week {week_number} ({week_type_label}) Routes", show=True)
                # Make markers visible by default for easier debugging now
                fg_outlet_markers = folium.FeatureGroup(name=f"Week {week_number} ({week_type_label}) Markers", show=True)
                week_has_content = False # Flag to check if anything was added for this week
                self.log_message(f"    Adding layers for Week {week_number} ({week_type_label})...")

                # Iterate through each day's route DataFrame in the list
                for day_index, day_df_original in enumerate(routes_list_for_week):
                    day_number = day_index + 1 # Day number 1-based
                    self.log_message(f"      Processing Day {day_number}...")
                    # Basic validation of the day's data
                    if not isinstance(day_df_original, pd.DataFrame) or day_df_original.empty:
                         self.log_message(f"        Skipping Day {day_number}: Invalid or empty DataFrame.")
                         continue

                    day_df = day_df_original.copy() # Work on a copy
                    required_map_cols = ['latitude', 'longitude', 'outletname', 'vf']
                    # Check essential columns exist *for this day's DataFrame*
                    if not all(col in day_df for col in required_map_cols):
                        missing_cols = set(required_map_cols) - set(day_df.columns)
                        self.log_message(f"        Skipping Day {day_number} due to missing columns: {missing_cols}.")
                        continue # Skip this day if essential info is missing

                    # Prepare data: Ensure 'Visit Order' exists and sort by it
                    if 'Visit Order' in day_df.columns and pd.api.types.is_numeric_dtype(day_df['Visit Order']):
                         day_df['Visit Order'] = pd.to_numeric(day_df['Visit Order'], errors='coerce').fillna(9999)
                         day_df_sorted = day_df.sort_values('Visit Order')
                    else:
                         self.log_message(f"        Warning: Visit Order missing or not numeric for Day {day_number}. Assigning sequential order.")
                         day_df['Visit Order'] = range(1, len(day_df) + 1) # Assign order if missing
                         day_df_sorted = day_df.sort_values('Visit Order') # Sort by assigned order

                    # Assign color for this day's route, cycling through the list
                    current_route_color = route_colors[(day_index + color_start_offset) % len(route_colors)]
                    valid_points_for_polyline = [] # Collect valid coords for the route line
                    markers_added_this_day = 0

                    # Iterate through outlets visited on this day
                    for visit_order_index, (_, outlet_row) in enumerate(day_df_sorted.iterrows()):
                        lat_val = outlet_row.get('latitude')
                        lon_val = outlet_row.get('longitude')
                        outlet_name_str = str(outlet_row.get('outletname', 'N/A'))
                        # self.log_message(f"          Checking outlet: {outlet_name_str} | Coords: {lat_val}, {lon_val}")

                        # Validate coordinates for this specific outlet
                        if pd.isna(lat_val) or pd.isna(lon_val):
                            self.log_message(f"          Warning: Skipping marker for '{outlet_name_str}' (Day {day_number}) due to missing lat/lon.")
                            continue # Skip marker if coords are missing

                        try:
                            # Convert valid coordinates to float for Folium
                            lat_float, lon_float = float(lat_val), float(lon_val)
                            valid_points_for_polyline.append([lat_float, lon_float]) # Add to list for line
                        except (ValueError, TypeError):
                            self.log_message(f"          Warning: Skipping marker for '{outlet_name_str}' (Day {day_number}) due to invalid coordinate type ({lat_val}, {lon_val}).")
                            continue # Skip marker if conversion fails

                        # --- Create Marker ---
                        vf_value = outlet_row.get('vf', 0)
                        visit_number = int(outlet_row.get('Visit Order', visit_order_index + 1)) # Use calculated order
                        marker_color = 'purple' if vf_value == 4 else 'blue'
                        marker_icon_name = 'star' if vf_value == 4 else 'info-sign'
                        popup_html_content = f"<b>{outlet_name_str}</b><br>W{week_number} D{day_number} - Visit #{visit_number}<br>VF: {vf_value}<br>Coords: ({lat_float:.5f}, {lon_float:.5f})"
                        tooltip_text = f"W{week_number}D{day_number} #{visit_number}: {outlet_name_str} (VF:{vf_value})"

                        marker_arguments = {
                            "location": [lat_float, lon_float],
                            "popup": folium.Popup(popup_html_content, max_width=300),
                            "tooltip": tooltip_text,
                            "icon": folium.Icon(color=marker_color, icon=marker_icon_name, prefix='glyphicon')
                        }
                        try:
                            # Add marker directly to the main weekly marker group
                            folium.Marker(**marker_arguments).add_to(fg_outlet_markers)
                            markers_added_this_day += 1
                            week_has_content = True # Mark that we have data to add for this week
                        except Exception as e_marker:
                            self.log_message(f"          Warning: Failed to add marker for '{outlet_name_str}' (Day {day_number}): {e_marker}")

                    # --- Create Polyline for the Day's Route ---
                    if len(valid_points_for_polyline) > 1: # Need at least 2 points for a line
                        self.log_message(f"        Adding polyline for Day {day_number} with {len(valid_points_for_polyline)} points.")
                        try:
                            folium.PolyLine(
                                locations=valid_points_for_polyline,
                                color=current_route_color,
                                weight=3,
                                opacity=0.8,
                                popup=f"Week {week_number}, Day {day_number} Route",
                                tooltip=f"W{week_number}D{day_number} ({len(valid_points_for_polyline)} stops)"
                            ).add_to(fg_route_lines) # Add line directly to route lines group
                            week_has_content = True # Also counts as content
                        except Exception as e_line:
                            self.log_message(f"        Warning: Failed to add route polyline for Day {day_number}: {e_line}")
                    elif len(valid_points_for_polyline) == 1:
                         self.log_message(f"        Warning: Only 1 valid point found for Day {day_number}, cannot draw polyline.")
                    else:
                         self.log_message(f"        No valid points found for polyline for Day {day_number}.")

                    self.log_message(f"      Finished Day {day_number}. Markers added: {markers_added_this_day}")


                # Add the main FeatureGroups for the week to the map if they contain content
                if week_has_content:
                    self.log_message(f"    Adding FeatureGroups for Week {week_number} to map.")
                    fg_route_lines.add_to(folium_map)
                    fg_outlet_markers.add_to(folium_map)
                else:
                    self.log_message(f"    No content added for Week {week_number}, skipping FeatureGroups.")

            # --- End Nested Function ---

            # Add routes and markers for Week 1 and Week 2 using the nested function
            add_week_routes_to_map(1, routes_week1, "A/C", color_start_offset=0)
            add_week_routes_to_map(2, routes_week2, "B/D", color_start_offset=len(routes_week1)) # Offset colors for week 2

            # Add Layer Control to allow toggling weeks/markers
            try:
                folium.LayerControl(collapsed=False).add_to(folium_map) # Keep layers expanded initially
                self.log_message("    Layer control added.")
            except Exception as e_layer:
                self.log_message(f"    Warning: Failed to add layer control: {e_layer}")

            # Fit map bounds if they were successfully calculated
            if map_bounds:
                 try:
                     folium_map.fit_bounds(map_bounds)
                     self.log_message(f"    Map bounds fit to: {map_bounds}")
                 except Exception as e_bounds:
                     self.log_message(f"    Warning: Failed to fit map bounds automatically: {e_bounds}")
            else:
                 self.log_message(f"    Map bounds not calculated, using default view centered at {map_center}")


            # --- Save the Map to HTML File ---
            try:
                 self.log_message(f"    Saving map for {rep_name} to: {map_filepath}")
                 folium_map.save(map_filepath)
                 self.log_message(f"  Successfully saved map for {rep_name}.")
                 # Store the path of the first successfully saved map
                 if first_map_filepath is None:
                     first_map_filepath = os.path.abspath(map_filepath)
            except Exception as e_save:
                self.log_message(f"ERROR saving map file for {rep_name} to '{map_filepath}': {e_save}")
                self.queue.put(('error', f"Map Save Failed ({rep_name}): {e_save}"))

            map_creation_count += 1 # Increment counter for progress

        # --- After Loop ---
        # If at least one map was created, ask the user (via queue) if they want to open the first one
        if first_map_filepath:
            self.queue.put(('ask_open_map', first_map_filepath))

        # Ensure progress bar completes for the map stage
        self.queue.put(('progress', progress_start + progress_range))
        self.log_message("--- Map Creation Process Finished ---")


    def disable_buttons(self):
        """Disables interactive widgets, typically during background processing."""
        widgets_to_disable = [
            # Buttons
            getattr(self, 'load_button', None),
            getattr(self, 'optimize_button', None),
            getattr(self, 'export_button', None),
            # Parameter Entries
            getattr(self, 'min_outlets_entry', None),
            getattr(self, 'max_outlets_entry', None),
            getattr(self, 'working_days_entry', None),
            getattr(self, 'solver_time_limit_entry', None)
        ]
        for widget in widgets_to_disable:
            # Check if widget exists and is a valid Tkinter widget
            if widget and isinstance(widget, (tk.Widget, ttk.Widget)) and widget.winfo_exists():
                try:
                    widget.config(state='disabled')
                except tk.TclError:
                    # Ignore error if widget is already destroyed (can happen during shutdown)
                    pass

    def enable_buttons(self):
        """Enables interactive widgets based on current app state (params, data, results). Called after processing."""
        self.log_message("Debug: Re-evaluating widget states after process completion.")
        try:
            # --- Parameter Entries ---
            # Always enable min outlets entry first, as others depend on it
            if hasattr(self, 'min_outlets_entry') and self.min_outlets_entry.winfo_exists():
                self.min_outlets_entry.config(state='normal')
            # Trigger validation chain which enables/disables subsequent entries and Load button
            self.validate_inputs()

            # --- Action Buttons ---
            # Re-check parameter validity explicitly here
            params_are_valid = self.validate_parameters() # This also logs if validation fails
            if params_are_valid:
                 self.log_message(f"Debug: Parameters validated in enable_buttons: {self.params}")


            # Check if data is loaded and not empty
            data_is_ready = self.outlets_data is not None and not self.outlets_data.empty

            # Determine state for Optimize button
            optimize_state = 'normal' if params_are_valid and data_is_ready else 'disabled'
            if hasattr(self, 'optimize_button') and self.optimize_button.winfo_exists():
                # Only update if state needs changing to avoid unnecessary GUI events
                if self.optimize_button.cget('state') != optimize_state:
                    self.optimize_button.config(state=optimize_state)
            self.log_message(f"Debug: Optimize button state set to '{optimize_state}' (Params Valid: {params_are_valid}, Data Ready: {data_is_ready})")

            # --- Check if schedule results exist and contain actual route data for export ---
            schedule_is_ready_for_export = False
            self.log_message("Debug: Starting schedule readiness check for export...")
            try:
                if not isinstance(self.schedule, dict):
                    self.log_message(f"Warning (enable_buttons): self.schedule is not a dictionary (type: {type(self.schedule)}). Export disabled.")
                elif not self.schedule: # Check if dict is empty
                    self.log_message("Debug (enable_buttons): self.schedule is an empty dictionary. Export disabled.")
                else:
                    self.log_message(f"Debug (enable_buttons): self.schedule is a dictionary with {len(self.schedule)} rep(s). Iterating...")
                    for rep_name, rep_schedule_entries in self.schedule.items():
                        if not isinstance(rep_schedule_entries, list):
                            self.log_message(f"Warning (enable_buttons): Schedule for rep '{rep_name}' is not a list (type: {type(rep_schedule_entries)}). Skipping rep for export check.")
                            continue # Move to the next representative's schedule

                        if not rep_schedule_entries: # Check if list of entries is empty
                            self.log_message(f"Debug (enable_buttons): Rep '{rep_name}' has an empty list of schedule entries. Skipping.")
                            continue

                        # self.log_message(f"Debug (enable_buttons): Rep '{rep_name}' has {len(rep_schedule_entries)} day entries. Checking entries...")
                        for day_entry_index, day_entry in enumerate(rep_schedule_entries):
                            if not isinstance(day_entry, dict):
                                self.log_message(f"Warning (enable_buttons): Day entry at index {day_entry_index} for rep '{rep_name}' is not a dictionary (type: {type(day_entry)}). Skipping entry.")
                                continue # Move to the next day's entry

                            route_df = day_entry.get('RouteDF') # Use .get() for safer access
                            if route_df is None: # Check if key 'RouteDF' exists
                                self.log_message(f"Warning (enable_buttons): Day entry at index {day_entry_index} for rep '{rep_name}' is missing 'RouteDF' key. Skipping entry.")
                                continue

                            if not isinstance(route_df, pd.DataFrame):
                                self.log_message(f"Warning (enable_buttons): 'RouteDF' for day entry at index {day_entry_index} (rep '{rep_name}') is not a pandas DataFrame (type: {type(route_df)}). Skipping entry.")
                                continue

                            if route_df.empty:
                                # self.log_message(f"Debug (enable_buttons): 'RouteDF' for day entry at index {day_entry_index} (rep '{rep_name}') is an empty DataFrame. Skipping this specific DF for export readiness.")
                                continue # This specific DF is empty, but others might be valid

                            # If we reach here, we found a valid, non-empty DataFrame
                            schedule_is_ready_for_export = True
                            self.log_message(f"Debug (enable_buttons): Found valid, non-empty RouteDF for rep '{rep_name}', day entry index {day_entry_index}. Schedule is ready for export.")
                            break # Exit inner loop (day_entries)
                        if schedule_is_ready_for_export:
                            break # Exit outer loop (reps)

            except (AttributeError, KeyError, TypeError) as e_struct:
                self.log_message(f"ERROR (enable_buttons): Exception ({type(e_struct).__name__}: {e_struct}) during schedule structure check. Assuming schedule not ready for export.")
                self.log_message(f"Traceback for schedule check error:\n{traceback.format_exc()}")
                schedule_is_ready_for_export = False # Ensure it's False on such errors
            except Exception as e_generic_check:
                # Catch any other unexpected errors during the check
                self.log_message(f"UNEXPECTED ERROR (enable_buttons): Exception ({type(e_generic_check).__name__}: {e_generic_check}) during schedule check. Assuming schedule not ready.")
                self.log_message(f"Traceback for generic schedule check error:\n{traceback.format_exc()}")
                schedule_is_ready_for_export = False

            # Determine state for Export button
            export_state = 'normal' if params_are_valid and data_is_ready and schedule_is_ready_for_export else 'disabled'
            if hasattr(self, 'export_button') and self.export_button.winfo_exists():
                 if self.export_button.cget('state') != export_state:
                    self.export_button.config(state=export_state)

            # Enhanced logging for final states
            self.log_message(f"Debug (enable_buttons) Final States: Params Valid={params_are_valid}, Data Ready={data_is_ready}, Schedule Ready for Export={schedule_is_ready_for_export}")
            self.log_message(f"Debug (enable_buttons): Optimize button state -> '{self.optimize_button.cget('state')}', Export button state -> '{export_state}'")

        except tk.TclError:
            # Can potentially happen if widgets are destroyed during state update (e.g., closing app)
            self.log_message("Debug: TclError encountered during enable_buttons, likely due to widget destruction.")
        except Exception as e:
            # Catch any other unexpected errors during button state logic
            self.log_message(f"ERROR encountered during enable_buttons logic: {e}\n{traceback.format_exc()}")


    def log_message(self, message: str):
        """Logs a message to both console and the GUI log Text widget via the queue."""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_entry = f"{timestamp} - {message}"
        print(log_entry) # Log to console immediately for debugging

        # Queue the message for GUI update (handled by the main thread via queue checker)
        # Add check for self.queue as well
        if hasattr(self, 'root') and self.root.winfo_exists() and hasattr(self, 'queue') and self.queue is not None:
            try:
                # Use a specific key ('log_gui') to indicate this message is for the GUI log
                self.queue.put(('log_gui', log_entry))
            except Exception as e:
                # Log queueing error to console if it occurs
                print(f"{timestamp} - ERROR: Failed to queue log message for GUI: {e}")
        # else: print(f"{timestamp} - Warning: Could not queue log for GUI (root or queue missing): {message}") # Optional debug

    def _log_message_gui(self, message: str):
        """Updates the GUI log Text widget. Should only be called from the main thread via queue checker."""
        try:
            # Check if the text widget exists and is valid
            if hasattr(self, 'results_text') and isinstance(self.results_text, tk.Text) and self.results_text.winfo_exists():
                # Simple log trimming mechanism to prevent excessive memory usage
                max_log_lines = 2500 # Keep a reasonable number of lines
                # Get current number of lines (approximate)
                num_lines = int(self.results_text.index('end-1c').split('.')[0])
                if num_lines > max_log_lines:
                    # If limit exceeded, delete oldest lines
                    lines_to_delete = num_lines - max_log_lines
                    self.results_text.config(state='normal')
                    self.results_text.delete('1.0', f'{lines_to_delete + 1}.0') # Delete from line 1 up to lines_to_delete+1
                    self.results_text.config(state='disabled')

                # Enable widget, insert message, scroll, disable widget
                self.results_text.config(state='normal')
                self.results_text.insert(tk.END, message + "\n")
                self.results_text.see(tk.END) # Auto-scroll to the bottom
                self.results_text.config(state='disabled')
        except tk.TclError:
             pass # Ignore if widget is destroyed while trying to update
        except Exception as e:
            # Log update error to console if GUI update fails
            timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            print(f"{timestamp} - ERROR: Failed to update GUI log widget: {e}")

    def show_error(self, message: str):
        """Logs an error and queues a request to display it in a messagebox."""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        full_error_msg = f"{timestamp} - ERROR: {message}"
        # Log the error immediately to console
        print(full_error_msg)
        # Also log it to the GUI log via queue
        if hasattr(self, 'queue') and self.queue is not None:
            self.queue.put(('log_gui', full_error_msg))
            # Queue the request to show the error box (handled by main thread)
            if hasattr(self, 'root') and self.root.winfo_exists():
                 self.queue.put(('_show_error_box_gui', str(message)))

    def _show_error_box_gui(self, message: str):
         """Actually displays the error messagebox. Called by queue handler in main thread."""
         if hasattr(self, 'root') and self.root.winfo_exists():
             messagebox.showerror("Application Error", message, parent=self.root)

    def show_warning(self, message: str):
        """Logs a warning and queues a request to display it in a messagebox."""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        full_warning_msg = f"{timestamp} - WARNING: {message}"
        # Log the warning immediately to console and GUI log
        print(full_warning_msg)
        if hasattr(self, 'queue') and self.queue is not None:
            self.queue.put(('log_gui', full_warning_msg))
            # Queue the request to show the warning box
            if hasattr(self, 'root') and self.root.winfo_exists():
                 self.queue.put(('_show_warning_box_gui', str(message)))

    def _show_warning_box_gui(self, message: str):
        """Actually displays the warning messagebox. Called by queue handler in main thread."""
        if hasattr(self, 'root') and self.root.winfo_exists():
            messagebox.showwarning("Application Warning", message, parent=self.root)

    def setup_queue_checker(self):
        """Sets up the periodic check of the inter-thread communication queue."""
        def check_queue_periodically():
            """Function run periodically to process messages from the queue."""
            messages_processed_this_cycle = 0
            # Limit messages processed per cycle to prevent freezing GUI if queue is flooded
            max_messages_per_cycle = 20
            try:
                while messages_processed_this_cycle < max_messages_per_cycle:
                    # Get message non-blockingly
                    # Add queue existence check
                    if not hasattr(self, 'queue') or self.queue is None:
                         break # Stop processing if queue is gone
                    msg_type, msg_payload = self.queue.get_nowait()
                    messages_processed_this_cycle += 1

                    try:
                        # --- Process different message types from the queue ---
                        if msg_type == 'log_gui':
                            self._log_message_gui(str(msg_payload))
                        elif msg_type == 'progress':
                            # Ensure progress value is float and within 0-100 range
                            progress_value = min(max(0.0, float(msg_payload)), 100.0)
                            if hasattr(self, 'progress_var'): # Check if var exists
                                 self.progress_var.set(progress_value)
                        elif msg_type == 'status':
                             if hasattr(self, 'status_var'): # Check if var exists
                                self.status_var.set(str(msg_payload))
                        elif msg_type == 'error':
                            # An error occurred in a background thread.
                            # The error message should already be logged.
                            # Update status bar and show the error dialog.
                            error_message = str(msg_payload)
                            self._show_error_box_gui(error_message)
                            if hasattr(self, 'status_var'): self.status_var.set("Error occurred. Check log.")
                            if hasattr(self, 'progress_var'): self.progress_var.set(0) # Reset progress on error
                        elif msg_type == 'warning':
                            # A warning occurred in a background thread.
                            # Warning should already be logged. Show the dialog.
                            self._show_warning_box_gui(str(msg_payload))
                        elif msg_type == '_show_error_box_gui': # Internal trigger
                            self._show_error_box_gui(str(msg_payload))
                        elif msg_type == '_show_warning_box_gui': # Internal trigger
                            self._show_warning_box_gui(str(msg_payload))
                        elif msg_type == 'ask_open_folder':
                            folder_path = str(msg_payload)
                            if isinstance(folder_path, str) and os.path.isdir(folder_path): # Check if it's a directory
                                if messagebox.askyesno("Export Complete", f"Results saved to folder:\n{folder_path}\n\nDo you want to open this folder now?", parent=self.root):
                                    self._open_file_or_folder(folder_path)
                            else:
                                self.log_message(f"Queue Info: Request to open folder ignored, path is not a valid directory: {folder_path}")
                        elif msg_type == 'ask_open_map':
                             map_filepath = str(msg_payload)
                             if isinstance(map_filepath, str) and os.path.isfile(map_filepath): # Check if it's a file
                                 map_filename = os.path.basename(map_filepath)
                                 if messagebox.askyesno("Map Ready", f"Route map generated:\n{map_filename}\n\nDo you want to open this map file now?", parent=self.root):
                                     self._open_file_or_folder(map_filepath)
                             else:
                                 self.log_message(f"Queue Info: Request to open map ignored, path is not a valid file: {map_filepath}")
                        elif msg_type == 'complete':
                            # A background task ('optimization' or 'export') has finished
                            task_name = str(msg_payload) if msg_payload else "process"
                            self.log_message(f"Debug: Queue received 'complete' signal for task '{task_name}'.")
                            self.processing = False # Mark processing as finished

                            # Update status bar based on task and outcome (unless already set to error)
                            current_status = ""
                            if hasattr(self, 'status_var') and self.status_var: # Check status_var exists
                                current_status = self.status_var.get().lower()

                            if "error" not in current_status and "fail" not in current_status:
                                # Check schedule state again after completion for status message
                                sched_has_data_final = False
                                if isinstance(self.schedule, dict) and self.schedule:
                                     try:
                                         # Using the same robust check logic as in enable_buttons
                                         for entries in self.schedule.values():
                                             if isinstance(entries, list) and entries:
                                                 for day_info in entries:
                                                     if isinstance(day_info, dict):
                                                         route_df = day_info.get('RouteDF')
                                                         if isinstance(route_df, pd.DataFrame) and not route_df.empty:
                                                             sched_has_data_final = True
                                                             break # Found one, enough to confirm data exists
                                                 if sched_has_data_final: break # Exit outer loop too
                                     except Exception: pass # Ignore check error here

                                final_status_msg = ""
                                if task_name == 'optimization':
                                    final_status_msg = "Optimization Complete. Ready to Export." if sched_has_data_final else "Optimization Complete (No schedule data)."
                                elif task_name == 'export':
                                     final_status_msg = "Export Complete. Ready."
                                else: # Generic completion
                                     final_status_msg = "Processing Complete. Ready."
                                if hasattr(self, 'status_var') and self.status_var: self.status_var.set(final_status_msg)


                            # Re-enable buttons based on the final state of data/results
                            self.enable_buttons()
                        else:
                             self.log_message(f"Warning: Unknown message type received in queue: {msg_type}")

                    except Exception as e_inner_process:
                        # Catch errors during the processing of a *specific* message type
                        print(f"ERROR processing queued message (Type: {msg_type}, Payload: {msg_payload}): {e_inner_process}\n{traceback.format_exc()}")
                        try: self.log_message(f"ERROR processing queued message ({msg_type}): {e_inner_process}")
                        except: pass # Avoid recursive errors if logging fails
                    finally:
                        # Mark task as done in the queue regardless of processing outcome
                        if hasattr(self, 'queue') and self.queue is not None:
                             try:
                                 self.queue.task_done()
                             except ValueError: # Can happen if task_done called too many times
                                 pass

            except QueueEmpty:
                # No more messages in the queue at this moment
                pass
            except Exception as e_outer_check:
                # Catch errors in the queue checking loop itself (e.g., error during get_nowait)
                print(f"CRITICAL ERROR in queue checker loop: {e_outer_check}\n{traceback.format_exc()}")
                try: self._log_message_gui(f"CRITICAL Queue checker loop error: {e_outer_check}")
                except: pass
            finally:
                # Schedule the next check after 100ms, ensuring it always runs
                # Add root existence check
                if hasattr(self, 'root') and self.root.winfo_exists():
                    self.root.after(100, check_queue_periodically)

        # --- Start the first check ---
        if hasattr(self, 'root') and self.root.winfo_exists():
            self.root.after(100, check_queue_periodically)

    def _open_file_or_folder(self, path: str):
        """Opens a file or folder using the default system application in a cross-platform way."""
        current_os = platform.system() # Store OS name here
        try:
            abs_path = os.path.abspath(path)
            if not os.path.exists(abs_path):
                self.log_message(f"Error opening path: Path not found at '{abs_path}'")
                # Use the queue mechanism to show the error box from the main thread
                if hasattr(self, 'queue') and self.queue is not None:
                    self.queue.put(('_show_error_box_gui', f"The specified file or folder could not be found:\n{abs_path}"))
                return # Stop further processing if path doesn't exist

            self.log_message(f"Attempting to open: {abs_path} on OS: {current_os}")

            # Use appropriate command based on OS
            if current_os == "Windows":
                # On Windows, os.startfile is generally preferred
                os.startfile(abs_path)
            elif current_os == "Darwin": # macOS
                # 'open' works for both files and folders on macOS
                subprocess.run(['open', abs_path], check=True, text=True) # Added text=True for clarity
            else: # Assume Linux/Unix-like
                # 'xdg-open' is the standard freedesktop way
                subprocess.run(['xdg-open', abs_path], check=True, text=True) # Added text=True for clarity

            self.log_message(f"Successfully launched command to open: {abs_path}")

        except FileNotFoundError:
            # This might happen if the command (open, xdg-open) isn't found or os.startfile isn't supported
            error_msg = f"Could not find the command to open files/folders on this system ({current_os}). Path: {abs_path}"
            self.log_message(f"Error opening path: {error_msg}")
            if hasattr(self, 'queue') and self.queue is not None: self.queue.put(('_show_error_box_gui', error_msg))
        except subprocess.CalledProcessError as e:
            # This happens if the subprocess command fails (e.g., permission denied)
            error_msg = f"Command to open path failed with error code {e.returncode}. Path: {abs_path}"
            self.log_message(f"Error opening path: {error_msg} - {e}")
            if hasattr(self, 'queue') and self.queue is not None: self.queue.put(('_show_error_box_gui', error_msg))
        except Exception as e:
            # Catch any other unexpected errors (e.g., os.startfile issues)
            error_msg = f"An unexpected error occurred while trying to open the path: {e}. Path: {abs_path}"
            self.log_message(f"Error opening path: {error_msg}\n{traceback.format_exc()}")
            if hasattr(self, 'queue') and self.queue is not None: self.queue.put(('_show_error_box_gui', error_msg))

# --- Main Execution ---
if __name__ == "__main__":
    # Log OR-Tools version
    print(f"Using OR-Tools version: {ortools.__version__}")
    print(f"Using Python version: {sys.version}")
    app = RouteOptimizationApp()
    app.root.mainloop()